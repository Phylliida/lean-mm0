"""A tiny Lean-4-flavoured surface parser.

Subset supported:
    def NAME [LEVEL_PARAMS] (BINDERS...) : TYPE := EXPR
    axiom NAME [LEVEL_PARAMS] (BINDERS...) : TYPE
    theorem NAME [LEVEL_PARAMS] (BINDERS...) : TYPE := EXPR

    BINDER  ::= '(' name ':' type ')'
    TYPE/EXPR forms:
        Sort N | Prop | Type N | Type      (Type = Sort 1, Prop = Sort 0)
        identifier
        identifier '.{' level (',' level)* '}'       universe instantiation
        '(' x ':' T ')' '->' U                       dependent Pi
        T '->' U                                     non-dep Pi
        '(' x ':' T ')' ',' B   inside `forall`/`∀`  dependent Pi
        'fun' '(' x ':' T ')' '=>' E                 lambda
        'lam' '(' x ':' T ')' '=>' E                 alternate spelling
        'let' x ':' T ':=' V ';' B                    let-bind
        f e1 e2 ...                                  application (left-assoc)
        '(' E ')'

This is deliberately a strict subset.  No implicit args, no type-class
instance args, no tactic blocks, no pattern matching.  Real Lean files
need the full elaborator; this parser is just a demonstrator that the
backend can consume textual input.
"""
from __future__ import annotations
import re
from dataclasses import dataclass
from typing import List, Optional, Tuple

from .levels import (
    Level, LZero, LSucc, LParam, level_succ,
)
from .expr import (
    Expr, Sort, BVar, FVar, Const, App, Lam, Pi, Let, Meta, By, Explicit,
    app_many,
)


# ---------------- tactic registry ----------------
# Tactic AST nodes are stored as Python tuples in a global registry; the
# `By(tac_id)` AST node carries an index into it.  Tactic forms:
#   ("exact", expr, bvar_stack)
#   ("rfl",)
#   ("intro", str)                 -- standalone; seq peels Pi off goal
#   ("apply", expr, bvar_stack)    -- apply f; <one tactic per subgoal>
#   ("assumption",)
#   ("rewrite", expr, bvar_stack)  -- rewrite h : a = b in the goal
#   ("cases", expr, bvar_stack)    -- case-split on a scrutinee
#   ("seq", [tac1, tac2, ...])

_TACTIC_REGISTRY: List[tuple] = []


def _register_tactic(tac: tuple) -> int:
    i = len(_TACTIC_REGISTRY)
    _TACTIC_REGISTRY.append(tac)
    return i


def get_tactic(tac_id: int) -> tuple:
    return _TACTIC_REGISTRY[tac_id]
from .env import Env, Definition, Axiom
from .kernel import Kernel, LocalCtx


# --------------- lexer ---------------

@dataclass
class Tok:
    kind: str            # 'id', 'num', 'punc', 'kw'
    text: str
    pos: int


KEYWORDS = {"def", "axiom", "theorem", "example", "instance",
            "inductive", "structure", "class", "extends",
            "infix", "infixl", "infixr",
            "fun", "lam", "let", "in",
            "Sort", "Type", "Prop", "forall", "match", "with", "where",
            "by", "exact", "rfl", "intro", "apply", "assumption",
            "rewrite", "rw", "cases",
            "if", "then", "else",
            "->", "=>", ":=", ":", ",", ";",
            "(", ")", ".{", "}", "|", "[", "]"}


def lex(src: str) -> List[Tok]:
    out: List[Tok] = []
    i = 0
    n = len(src)
    while i < n:
        c = src[i]
        if c.isspace():
            i += 1
            continue
        if c == '-' and i + 1 < n and src[i + 1] == '-':
            while i < n and src[i] != '\n':
                i += 1
            continue
        if src.startswith(":=", i):
            out.append(Tok("punc", ":=", i)); i += 2; continue
        if src.startswith("->", i):
            out.append(Tok("punc", "->", i)); i += 2; continue
        if src.startswith("=>", i):
            out.append(Tok("punc", "=>", i)); i += 2; continue
        if src.startswith(".{", i):
            out.append(Tok("punc", ".{", i)); i += 2; continue
        if c in "():,;{}|[]@":
            out.append(Tok("punc", c, i)); i += 1; continue
        matched = False
        for op in ("<=", ">=", "==", "!=", "&&", "||"):
            if src.startswith(op, i):
                out.append(Tok("sym", op, i)); i += len(op); matched = True; break
        if matched:
            continue
        if c in "+-*<>=!":
            out.append(Tok("sym", c, i)); i += 1; continue
        if c.isdigit():
            j = i
            while j < n and src[j].isdigit():
                j += 1
            out.append(Tok("num", src[i:j], i)); i = j; continue
        if c.isalpha() or c == "_":
            j = i
            while j < n and (src[j].isalnum() or src[j] in "_."):
                # don't swallow `.` if it's the start of a `.{` universe-args token
                if src[j] == "." and j + 1 < n and src[j + 1] == "{":
                    break
                j += 1
            text = src[i:j]
            kind = "kw" if text in {"def", "axiom", "theorem", "example",
                                    "instance", "inductive", "structure", "class",
                                    "extends", "infix", "infixl", "infixr",
                                    "fun", "lam", "let", "in",
                                    "Sort", "Type", "Prop",
                                    "forall", "match", "with", "where",
                                    "by", "exact", "rfl", "intro",
                                    "apply", "assumption",
                                    "rewrite", "rw", "cases",
                                    "if", "then", "else"} else "id"
            out.append(Tok(kind, text, i)); i = j; continue
        raise SyntaxError(f"unexpected character {c!r} at {i}")
    return out


# --------------- parser ---------------

class P:
    def __init__(self, toks: List[Tok], src: str, env=None,
                 infix_table=None):
        self.toks = toks
        self.i = 0
        self.src = src
        self.env = env
        self.infix_table: Dict[str, Tuple[int, str, str]] = \
            infix_table if infix_table is not None else {}
        # If we're parsing a def's body, this is the name of the def
        # (so recursive calls in a `match` body get compiled to the
        # recursor's IH).
        self.current_decl_name: Optional[str] = None
        self.current_rec_arg_idx: Optional[int] = None
        # The def's binders (name, type, implicit, inst_implicit) so a
        # `match` on a BVar can recover the scrutinee's type.
        self.current_decl_binders: Optional[List[Tuple[str, Expr, bool, bool]]] = None

    def peek(self) -> Optional[Tok]:
        return self.toks[self.i] if self.i < len(self.toks) else None

    def take(self) -> Tok:
        t = self.toks[self.i]
        self.i += 1
        return t

    def eat(self, text: str) -> Tok:
        t = self.peek()
        if t is None or t.text != text:
            raise SyntaxError(
                f"expected {text!r}, got {t.text if t else 'EOF'!r} near "
                f"{self.src[max(0, (t.pos if t else len(self.src))-30):]!r}")
        return self.take()

    def at(self, text: str) -> bool:
        t = self.peek()
        return t is not None and t.text == text

    def at_kind(self, kind: str) -> bool:
        t = self.peek()
        return t is not None and t.kind == kind

    # ---- decls ----

    def parse_program(self) -> List[Tuple[str, str, Tuple[str, ...],
                                          List[Tuple[str, "Expr"]],
                                          "Expr", Optional["Expr"]]]:
        """Returns list of (kind, name, level_params, binders, ty, body|None)
        where binders contributing to TYPE are absorbed into a leading Pi.
        """
        decls: List[Tuple[str, str, Tuple[str, ...],
                          List[Tuple[str, Expr]], Expr, Optional[Expr]]] = []
        while self.peek() is not None:
            decls.append(self.parse_decl())
        return decls

    def parse_decl(self):
        nxt = self.peek()
        if nxt and nxt.text == "inductive":
            return self._parse_inductive()
        if nxt and nxt.text in ("structure", "class"):
            return self._parse_structure()
        if nxt and nxt.text in ("infix", "infixl", "infixr"):
            return self._parse_infix()
        kw = self.take()
        if kw.text not in {"def", "axiom", "theorem", "example", "instance"}:
            raise SyntaxError(f"expected def/axiom/theorem/example/instance, got {kw.text!r}")
        if kw.text == "example":
            # generate a fresh unique name
            P._example_counter = getattr(P, "_example_counter", 0) + 1
            name = f"_example_{P._example_counter}"
        else:
            name = self.take().text
        lvl_params: Tuple[str, ...] = ()
        if self.at(".{"):
            self.take()
            # allow empty `.{}`
            params: List[str] = []
            if not self.at("}"):
                params.append(self.take().text)
                while self.at(","):
                    self.take()
                    params.append(self.take().text)
            self.eat("}")
            lvl_params = tuple(params)
        # binders: (nm, dom, implicit_flag, inst_implicit_flag)
        binders: List[Tuple[str, Expr, bool, bool]] = []
        while self.at("(") or self.at("{") or self.at("["):
            opener = self.peek().text
            closer = {"(": ")", "{": "}", "[": "]"}[opener]
            implicit = (opener == "{")
            inst_implicit = (opener == "[")
            save = self.i
            ok = False
            try:
                self.eat(opener)
                names = []
                first = self.take()
                if first.kind != "id":
                    raise SyntaxError("binder name expected")
                names.append(first.text)
                while self.at_kind("id"):
                    names.append(self.take().text)
                self.eat(":")
                ty = self.parse_expr(lvl_params, [b[0] for b in binders])
                self.eat(closer)
                from .expr import shift as _shift_expr
                for k, nm in enumerate(names):
                    binders.append((nm, _shift_expr(ty, k), implicit, inst_implicit))
                ok = True
            except SyntaxError:
                pass
            if ok:
                continue
            # Anonymous binder (Lean style `[T]`): only for inst-implicit.
            if inst_implicit:
                self.i = save
                try:
                    self.eat(opener)
                    ty = self.parse_expr(lvl_params, [b[0] for b in binders])
                    self.eat(closer)
                    anon = f"_inst_{len(binders)}"
                    binders.append((anon, ty, False, True))
                    continue
                except SyntaxError:
                    pass
            self.i = save
            break
        # ': TYPE'
        self.eat(":")
        ty_inner = self.parse_expr(lvl_params, [b[0] for b in binders])
        ty: Expr = ty_inner
        for nm, dom, impl, inst_impl in reversed(binders):
            ty = Pi(nm, dom, ty, impl, inst_impl)
        body: Optional[Expr] = None
        if self.at(":="):
            self.take()
            # During body parsing, expose the def's name so a top-level
            # `match` on the recursive arg can compile recursive calls
            # to the recursor's IH.
            saved_name = self.current_decl_name
            saved_rec = self.current_rec_arg_idx
            saved_binders = self.current_decl_binders
            self.current_decl_name = name
            self.current_rec_arg_idx = None
            self.current_decl_binders = list(binders)
            try:
                body_inner = self.parse_expr(lvl_params, [b[0] for b in binders])
            finally:
                self.current_decl_name = saved_name
                self.current_rec_arg_idx = saved_rec
                self.current_decl_binders = saved_binders
            body = body_inner
            for nm, dom, _impl, _inst_impl in reversed(binders):
                body = Lam(nm, dom, body)
        # `example` is treated like a theorem internally
        kind = "theorem" if kw.text == "example" else kw.text
        return (kind, name, lvl_params, binders, ty, body)

    # ---- inductive / structure ----

    def _parse_lvl_params(self) -> Tuple[str, ...]:
        if not self.at(".{"):
            return ()
        self.take()
        params: List[str] = []
        if not self.at("}"):
            params.append(self.take().text)
            while self.at(","):
                self.take()
                params.append(self.take().text)
        self.eat("}")
        return tuple(params)

    def _parse_binders(self, lvl_params, current_binders):
        """Parse a sequence of (a b : T), {a : T}, [a : T] or [T] binders."""
        from .expr import shift as _shift
        bs: List[Tuple[str, Expr, bool, bool]] = []
        while self.at("(") or self.at("{") or self.at("["):
            opener = self.peek().text
            closer = {"(": ")", "{": "}", "[": "]"}[opener]
            implicit = (opener == "{")
            inst_implicit = (opener == "[")
            save = self.i
            ok = False
            try:
                self.eat(opener)
                names = []
                first = self.take()
                if first.kind != "id":
                    raise SyntaxError("binder name expected")
                names.append(first.text)
                while self.at_kind("id"):
                    names.append(self.take().text)
                self.eat(":")
                ty = self.parse_expr(
                    lvl_params,
                    [b[0] for b in current_binders] + [b[0] for b in bs])
                self.eat(closer)
                for k, nm in enumerate(names):
                    bs.append((nm, _shift(ty, k), implicit, inst_implicit))
                ok = True
            except SyntaxError:
                pass
            if ok:
                continue
            if inst_implicit:
                self.i = save
                try:
                    self.eat(opener)
                    ty = self.parse_expr(
                        lvl_params,
                        [b[0] for b in current_binders] + [b[0] for b in bs])
                    self.eat(closer)
                    anon = f"_inst_{len(current_binders) + len(bs)}"
                    bs.append((anon, ty, False, True))
                    continue
                except SyntaxError:
                    pass
            self.i = save
            break
        return bs

    def _parse_inductive(self):
        self.eat("inductive")
        name = self.take().text
        lvl_params = self._parse_lvl_params()
        params = self._parse_binders(lvl_params, [])
        self.eat(":")
        result_ty = self.parse_expr(lvl_params, [p[0] for p in params])
        self.eat("where")
        ctors = []
        while self.at("|"):
            self.take()
            ctor_name = self.take().text
            ctor_fields = self._parse_binders(
                lvl_params, list(params))
            self.eat(":")
            ctor_ret = self.parse_expr(
                lvl_params,
                [p[0] for p in params] + [f[0] for f in ctor_fields])
            ctors.append((ctor_name, ctor_fields, ctor_ret))
        return ("inductive", name, lvl_params, params, result_ty, ctors)

    def _parse_infix(self):
        # `infix[:prec] OP FUNC` (non-assoc, default prec 65)
        # `infixl[:prec] OP FUNC` (left-associative)
        # `infixr[:prec] OP FUNC` (right-associative)
        kw = self.take().text
        assoc = {"infix": "none", "infixl": "left", "infixr": "right"}[kw]
        prec = 65
        if self.at(":"):
            self.take()
            tok = self.take()
            if tok.kind != "num":
                raise SyntaxError(f"infix expects a number after :, got {tok.text!r}")
            prec = int(tok.text)
        op_tok = self.take()
        if op_tok.kind != "sym":
            raise SyntaxError(f"infix expects a symbol, got {op_tok.text!r}")
        func_tok = self.take()
        if func_tok.kind != "id":
            raise SyntaxError(f"infix expects a function name, got {func_tok.text!r}")
        return ("infix", op_tok.text, (), [], None,
                [func_tok.text, prec, assoc])

    def _parse_structure(self):
        # structure / class Name [.{lvls}] (params) [: TYPE] where (field : T) ...
        kw = self.take()                                    # "structure" or "class"
        is_class = (kw.text == "class")
        name = self.take().text
        lvl_params = self._parse_lvl_params()
        params = self._parse_binders(lvl_params, [])
        # optional explicit result type
        if self.at(":"):
            self.take()
            result_ty = self.parse_expr(lvl_params, [p[0] for p in params])
        else:
            from .levels import LSucc, LZero
            result_ty = Sort(LSucc(LZero()))
        # optional extends clause:  extends T1, T2, ...
        extends_clauses: List[Expr] = []
        if self.at("extends"):
            self.take()
            extends_clauses.append(self.parse_app(lvl_params, [p[0] for p in params]))
            while self.at(","):
                self.take()
                extends_clauses.append(self.parse_app(lvl_params, [p[0] for p in params]))
        self.eat("where")
        # fields: each one `(name : T)`.  Bare `name : T` is also accepted,
        # but only when there's a single field (the parser can't otherwise
        # tell where one field ends and the next begins without parens).
        fields = []
        while True:
            if self.at("("):
                save = self.i
                try:
                    self.eat("(")
                    fname_tok = self.take()
                    if fname_tok.kind != "id":
                        raise SyntaxError("field name expected")
                    self.eat(":")
                    fty = self.parse_expr(
                        lvl_params,
                        [p[0] for p in params] + [f[0] for f in fields])
                    self.eat(")")
                    fields.append((fname_tok.text, fty, False, False))
                    continue
                except SyntaxError:
                    self.i = save
                    break
            if self.at_kind("id") and not self._next_keyword():
                # bare form: only safe as the final field
                fname = self.take().text
                self.eat(":")
                fty = self.parse_expr(
                    lvl_params,
                    [p[0] for p in params] + [f[0] for f in fields])
                fields.append((fname, fty, False, False))
                break
            break
        # Prepend each `extends T` as a synthetic field named `to<Parent>`.
        # User-written field types were parsed assuming scope =
        # [params + user_fields_so_far], so they need to be shifted to
        # account for the additional `extends`-fields prepended below.
        if extends_clauses:
            from .expr import shift as _shft
            extended_fields = []
            for k, parent_ty in enumerate(extends_clauses):
                head_e = parent_ty
                while isinstance(head_e, App):
                    head_e = head_e.fn
                if not isinstance(head_e, Const):
                    raise SyntaxError(
                        f"extends clause must be a class application; got {head_e}")
                parent_name = head_e.name.split(".")[-1]
                field_name = f"to{parent_name}"
                # Shift parent_ty up by k (for prior extends fields in scope).
                shifted = _shft(parent_ty, k)
                extended_fields.append((field_name, shifted, False, False))
            n_ext = len(extends_clauses)
            # Shift each user-written field's type up by n_ext, but
            # with a cutoff that preserves references to previous user
            # fields.  Field at index j has access to params + first j
            # user fields, so cutoff = j.
            shifted_user_fields = []
            for j, (fn, fty, fi, fii) in enumerate(fields):
                shifted_user_fields.append(
                    (fn, _shft(fty, n_ext, j), fi, fii))
            fields = extended_fields + shifted_user_fields
        return ("structure", name, lvl_params, params, result_ty, fields, is_class)

    def _next_keyword(self) -> bool:
        """Return True if the current token starts a new top-level form."""
        t = self.peek()
        if t is None:
            return True
        return t.kind == "kw" and t.text in {
            "def", "axiom", "theorem", "instance", "inductive", "structure"}

    # ---- expressions ----

    def parse_expr(self, lvl_params: Tuple[str, ...],
                   bvar_stack: List[str]) -> Expr:
        return self.parse_arrow(lvl_params, bvar_stack)

    def parse_arrow(self, lvl_params, bvar_stack) -> Expr:
        left = self.parse_binop(lvl_params, bvar_stack)
        if self.at("->"):
            self.take()
            right = self.parse_arrow(lvl_params, bvar_stack + ["_"])
            return Pi("_", left, right)
        return left

    def parse_binop(self, lvl_params, bvar_stack, min_prec: int = 0) -> Expr:
        """Pratt-style precedence climbing.  Each registered operator
        has (prec, assoc, func).  Parses `app (OP rhs)*` where OP's
        prec >= min_prec; rhs is parsed at min_prec + (1 if left else 0)."""
        left = self.parse_app(lvl_params, bvar_stack)
        while True:
            t = self.peek()
            if t is None or t.kind != "sym" or t.text not in self.infix_table:
                break
            prec, assoc, func_name = self.infix_table[t.text]
            if prec < min_prec:
                break
            self.take()
            next_min = prec + (1 if assoc != "right" else 0)
            right = self.parse_binop(lvl_params, bvar_stack, next_min)
            left = App(App(Const(func_name, ()), left), right)
        return left

    def parse_app(self, lvl_params, bvar_stack) -> Expr:
        head = self.parse_atom(lvl_params, bvar_stack)
        while True:
            t = self.peek()
            if t is None:
                break
            if t.text in {")", ":=", "->", "=>", ",", ";", "in", ":", "}", "]", "|"}:
                break
            if t.kind == "sym":
                break
            if t.kind == "kw" and t.text not in {"Sort", "Type", "Prop"}:
                break
            arg = self.parse_atom(lvl_params, bvar_stack)
            head = App(head, arg)
        return head

    def parse_atom(self, lvl_params, bvar_stack) -> Expr:
        t = self.peek()
        if t is None:
            raise SyntaxError("unexpected EOF")
        if t.text in ("(", "{", "["):
            opener = t.text
            closer = {"(": ")", "{": "}", "[": "]"}[opener]
            implicit = (opener == "{")
            inst_implicit = (opener == "[")
            self.take()
            save = self.i
            try:
                nm = self.take()
                if nm.kind != "id":
                    raise SyntaxError("not a binder")
                self.eat(":")
                ty = self.parse_expr(lvl_params, bvar_stack)
                self.eat(closer)
                if self.at("->"):
                    self.take()
                    body = self.parse_arrow(lvl_params, bvar_stack + [nm.text])
                    return Pi(nm.text, ty, body, implicit, inst_implicit)
                raise SyntaxError("expected -> after binder")
            except SyntaxError:
                self.i = save
                e = self.parse_expr(lvl_params, bvar_stack)
                self.eat(closer)
                return e
        if t.text == "fun" or t.text == "lam":
            self.take()
            # Accept one or more (name1 name2 ... : T) blocks before `=>`.
            from .expr import shift as _shift_e
            collected: List[Tuple[str, Expr]] = []  # (name, type-at-its-binding-position)
            while self.at("("):
                self.eat("(")
                names = []
                first = self.take()
                if first.kind != "id":
                    raise SyntaxError("binder name expected")
                names.append(first.text)
                while self.at_kind("id"):
                    names.append(self.take().text)
                self.eat(":")
                ty = self.parse_expr(
                    lvl_params,
                    bvar_stack + [nm for nm, _ in collected])
                self.eat(")")
                base = len(collected)
                for k, nm in enumerate(names):
                    collected.append((nm, _shift_e(ty, k)))
            if not collected:
                raise SyntaxError("fun needs at least one binder")
            self.eat("=>")
            body = self.parse_expr(
                lvl_params,
                bvar_stack + [nm for nm, _ in collected])
            for nm, ty in reversed(collected):
                body = Lam(nm, ty, body)
            return body
        if t.text == "forall":
            self.take()
            self.eat("(")
            nm = self.take()
            self.eat(":")
            ty = self.parse_expr(lvl_params, bvar_stack)
            self.eat(")")
            self.eat(",")
            body = self.parse_expr(lvl_params, bvar_stack + [nm.text])
            return Pi(nm.text, ty, body)
        if t.text == "@":
            self.take()
            from .expr import Explicit as _Explicit
            inner = self.parse_atom(lvl_params, bvar_stack)
            return _Explicit(inner)
        if t.text == "by":
            self.take()
            tac = self._parse_tactics(lvl_params, bvar_stack)
            tac_id = _register_tactic(tac)
            return By(tac_id)
        if t.text == "match":
            self.take()
            # Optional `(motive := M)` annotation before the scrutinee.
            # When supplied, the compiler uses M directly as the recursor's
            # motive (dependent), and skips the non-dependent fast paths.
            motive_override = None
            if (self.at("(") and self.i + 1 < len(self.toks)
                    and self.toks[self.i + 1].text == "motive"):
                self.take()                      # '('
                self.take()                      # 'motive'
                self.eat(":=")
                motive_override = self.parse_expr(lvl_params, bvar_stack)
                self.eat(")")
            scrutinee = self.parse_app(lvl_params, bvar_stack)
            if motive_override is not None:
                # The result type can be derived from M applied to scrut.
                result_ty = App(motive_override, scrutinee)
            else:
                self.eat(":")
                result_ty = self.parse_arrow(lvl_params, bvar_stack)
            self.eat("with")
            arms = []
            while self.at("|"):
                self.take()
                ctor = self.take().text
                pat_vars: List[str] = []
                while self.at_kind("id"):
                    pat_vars.append(self.take().text)
                self.eat("=>")
                rhs = self.parse_expr(lvl_params, bvar_stack + pat_vars)
                arms.append((ctor, pat_vars, rhs))
            # Detect structural recursion: if the scrutinee is a single
            # BVar (the def's arg) and we're at the body's top level,
            # `current_decl_name` becomes the rec_name for IH compilation.
            rec_name = None
            scrut_ty_hint = None
            rec_arg_pos = -1
            if isinstance(scrutinee, BVar) and self.current_decl_name is not None:
                rec_name = self.current_decl_name
                if self.current_decl_binders is not None:
                    binder_list = self.current_decl_binders
                    idx_from_end = scrutinee.idx
                    if idx_from_end < len(binder_list):
                        b = binder_list[-(idx_from_end + 1)]
                        from .expr import shift as _shft
                        scrut_ty_hint = _shft(b[1], 1 + scrutinee.idx)
                        # Compute the rec arg's position in user-PARSED
                        # recursive calls: matched arg's decl-index minus
                        # the number of implicit binders before it.
                        matched_decl_idx = len(binder_list) - 1 - idx_from_end
                        n_implicit_before = sum(
                            1 for bdr in binder_list[:matched_decl_idx]
                            if bdr[2] or bdr[3])
                        rec_arg_pos = matched_decl_idx - n_implicit_before
            return _compile_match(scrutinee, result_ty, arms, self.env,
                                  lvl_params, bvar_stack, rec_name=rec_name,
                                  scrut_ty_hint=scrut_ty_hint,
                                  rec_arg_pos=rec_arg_pos,
                                  motive_override=motive_override)
        if t.text == "let":
            self.take()
            nm = self.take()
            self.eat(":")
            ty = self.parse_expr(lvl_params, bvar_stack)
            self.eat(":=")
            val = self.parse_expr(lvl_params, bvar_stack)
            self.eat(";")
            body = self.parse_expr(lvl_params, bvar_stack + [nm.text])
            return Let(nm.text, ty, val, body)
        if t.text == "Sort":
            self.take()
            # accept Sort with or without explicit level (default 0)
            if self.at_kind("num") or self.at_kind("id") or self.at("("):
                lvl = self.parse_level(lvl_params)
            else:
                lvl = LZero()
            return Sort(lvl)
        if t.text == "Type":
            self.take()
            # `Type` alone = Type 0 = Sort 1; `Type u` = Sort (succ u)
            if self.at_kind("num") or self.at_kind("id") or self.at("("):
                lvl = self.parse_level(lvl_params)
            else:
                lvl = LZero()
            return Sort(level_succ(lvl))
        if t.text == "Prop":
            self.take()
            return Sort(LZero())
        if t.text == "if":
            self.take()
            c = self.parse_expr(lvl_params, bvar_stack)
            self.eat("then")
            a = self.parse_expr(lvl_params, bvar_stack)
            self.eat("else")
            b = self.parse_expr(lvl_params, bvar_stack)
            # Desugar to `@ite _ c _ a b`: the level meta + α + d are
            # filled by the elaborator.  `@` disables auto-implicit
            # insertion so our manual holes line up with ite's binders.
            HOLE = Const("_", ())
            ite_head = Explicit(Const("ite", ()))
            return app_many(ite_head, HOLE, c, HOLE, a, b)
        if t.kind == "id":
            self.take()
            # check for level-instance:  ident.{l1, l2}
            level_args: Tuple[Level, ...] = ()
            if self.at(".{"):
                self.take()
                lvls = [self.parse_level(lvl_params)]
                while self.at(","):
                    self.take()
                    lvls.append(self.parse_level(lvl_params))
                self.eat("}")
                level_args = tuple(lvls)
            # `_` in expression position is always a hole, never a BVar
            # — the elaborator turns it into a fresh meta.
            if t.text == "_" and not level_args:
                return Const("_", ())
            # BVar lookup
            if t.text in bvar_stack and not level_args:
                # find innermost occurrence
                for k in range(len(bvar_stack) - 1, -1, -1):
                    if bvar_stack[k] == t.text:
                        return BVar(len(bvar_stack) - 1 - k)
            return Const(t.text, level_args)
        if t.kind == "num":
            # numeric literal — by convention treat as Nat literal
            n = int(t.text)
            self.take()
            e: Expr = Const("Nat.zero", ())
            for _ in range(n):
                e = App(Const("Nat.succ", ()), e)
            return e
        raise SyntaxError(f"unexpected token {t.text!r}")

    # ---- tactics ----

    def _parse_tactics(self, lvl_params, bvar_stack) -> tuple:
        """Parse a tactic block: tac1; tac2; ...  (sequence).

        Threads `bvar_stack` so an `intro x` makes `x` parseable as a
        BVar reference in subsequent tactics."""
        first = self._parse_single_tactic(lvl_params, bvar_stack)
        if first[0] == "intro":
            bvar_stack = bvar_stack + [first[1]]
        if not self.at(";"):
            return first
        tacs = [first]
        while self.at(";"):
            self.take()
            nxt = self._parse_single_tactic(lvl_params, bvar_stack)
            tacs.append(nxt)
            if nxt[0] == "intro":
                bvar_stack = bvar_stack + [nxt[1]]
        return ("seq", tacs)

    def _parse_single_tactic(self, lvl_params, bvar_stack) -> tuple:
        t = self.peek()
        if t is None:
            raise SyntaxError("expected tactic")
        if t.text == "rfl":
            self.take()
            return ("rfl",)
        if t.text == "exact":
            self.take()
            e = self.parse_expr(lvl_params, bvar_stack)
            return ("exact", e, list(bvar_stack))
        if t.text == "apply":
            self.take()
            e = self.parse_expr(lvl_params, bvar_stack)
            return ("apply", e, list(bvar_stack))
        if t.text == "assumption":
            self.take()
            return ("assumption",)
        if t.text in ("rewrite", "rw"):
            self.take()
            e = self.parse_expr(lvl_params, bvar_stack)
            return ("rewrite", e, list(bvar_stack))
        if t.text == "cases":
            self.take()
            e = self.parse_expr(lvl_params, bvar_stack)
            return ("cases", e, list(bvar_stack))
        if t.text == "intro":
            self.take()
            name_tok = self.take()
            if name_tok.kind != "id":
                raise SyntaxError("intro expects a name")
            # `intro` is a standalone tactic.  When it appears inside a
            # `;`-sequence the seq interpreter peels a Pi binder off the
            # current goal, pushes the introduced var onto the local
            # context, and lets subsequent tactics see it.  This is
            # different from older designs where intro would swallow the
            # rest of the sequence as its body — that nested form made
            # subgoals from later tactics (e.g. `apply`) unable to be
            # solved by anything after the intro.
            return ("intro", name_tok.text)
        raise SyntaxError(f"unknown tactic {t.text!r}")

    def parse_level(self, lvl_params: Tuple[str, ...]) -> Level:
        t = self.peek()
        if t is None:
            raise SyntaxError("expected level")
        # parenthesised level
        if t.text == "(":
            self.take()
            l = self.parse_level(lvl_params)
            self.eat(")")
            return l
        # max u v / imax u v
        if t.kind == "id" and t.text in ("max", "imax"):
            op = self.take().text
            a = self._parse_level_atom(lvl_params)
            b = self._parse_level_atom(lvl_params)
            from .levels import LMax as _LMax, LIMax as _LIMax
            return _LMax(a, b) if op == "max" else _LIMax(a, b)
        return self._parse_level_atom(lvl_params)

    def _parse_level_atom(self, lvl_params: Tuple[str, ...]) -> Level:
        t = self.peek()
        if t is None:
            raise SyntaxError("expected level")
        if t.text == "(":
            self.take()
            l = self.parse_level(lvl_params)
            self.eat(")")
            return l
        if t.kind == "num":
            self.take()
            l: Level = LZero()
            for _ in range(int(t.text)):
                l = LSucc(l)
            return l
        if t.kind == "id":
            self.take()
            return LParam(t.text)
        raise SyntaxError(f"expected level, got {t.text!r}")


def _replace_rec_call(e: Expr, rec_name: str,
                      target_bvar_idx: int, sentinel_name: str,
                      rec_arg_pos: int = -1) -> Expr:
    """Walk e; whenever we find an App-spine whose head is
    `Const(rec_name)` and whose argument at position `rec_arg_pos`
    (0-indexed from the left, in the user's PARSED call — i.e. NOT
    counting implicits the elaborator will insert) is
    `BVar(target_bvar_idx)`, replace the whole spine with
    `FVar(sentinel_name)`.

    If `rec_arg_pos == -1`, fall back to "last arg" detection (used
    by the Nat-fast-path)."""
    if isinstance(e, App):
        head = e
        args = []
        while isinstance(head, App):
            args.insert(0, head.arg)
            head = head.fn
        match = False
        if isinstance(head, Const) and head.name == rec_name and args:
            if rec_arg_pos == -1:
                idx = len(args) - 1
            else:
                idx = rec_arg_pos
            if 0 <= idx < len(args):
                a = args[idx]
                if isinstance(a, BVar) and a.idx == target_bvar_idx:
                    match = True
        if match:
            from .expr import Sort as _Sort
            return FVar(sentinel_name, _Sort(LZero()))
        return App(_replace_rec_call(e.fn, rec_name, target_bvar_idx, sentinel_name, rec_arg_pos),
                   _replace_rec_call(e.arg, rec_name, target_bvar_idx, sentinel_name, rec_arg_pos))
    if isinstance(e, (Sort, BVar, FVar, Const, Meta)):
        return e
    if isinstance(e, Lam):
        return Lam(e.binder,
                   _replace_rec_call(e.dom, rec_name, target_bvar_idx, sentinel_name, rec_arg_pos),
                   _replace_rec_call(e.body, rec_name, target_bvar_idx + 1, sentinel_name, rec_arg_pos))
    if isinstance(e, Pi):
        return Pi(e.binder,
                  _replace_rec_call(e.dom, rec_name, target_bvar_idx, sentinel_name, rec_arg_pos),
                  _replace_rec_call(e.body, rec_name, target_bvar_idx + 1, sentinel_name, rec_arg_pos),
                  e.implicit, e.inst_implicit)
    if isinstance(e, Let):
        return Let(e.binder,
                   _replace_rec_call(e.type_, rec_name, target_bvar_idx, sentinel_name, rec_arg_pos),
                   _replace_rec_call(e.value, rec_name, target_bvar_idx, sentinel_name, rec_arg_pos),
                   _replace_rec_call(e.body, rec_name, target_bvar_idx + 1, sentinel_name, rec_arg_pos))
    return e


def _replace_fvar_with_bvar(e: Expr, name: str, target_bvar_idx: int) -> Expr:
    """Replace FVar(name) occurrences with BVar(target_bvar_idx).  Adjusts
    target_bvar_idx through binders."""
    if isinstance(e, FVar) and e.name == name:
        return BVar(target_bvar_idx)
    if isinstance(e, (Sort, BVar, Const, Meta)):
        return e
    if isinstance(e, App):
        return App(_replace_fvar_with_bvar(e.fn, name, target_bvar_idx),
                   _replace_fvar_with_bvar(e.arg, name, target_bvar_idx))
    if isinstance(e, Lam):
        return Lam(e.binder,
                   _replace_fvar_with_bvar(e.dom, name, target_bvar_idx),
                   _replace_fvar_with_bvar(e.body, name, target_bvar_idx + 1))
    if isinstance(e, Pi):
        return Pi(e.binder,
                  _replace_fvar_with_bvar(e.dom, name, target_bvar_idx),
                  _replace_fvar_with_bvar(e.body, name, target_bvar_idx + 1),
                  e.implicit, e.inst_implicit)
    if isinstance(e, Let):
        return Let(e.binder,
                   _replace_fvar_with_bvar(e.type_, name, target_bvar_idx),
                   _replace_fvar_with_bvar(e.value, name, target_bvar_idx),
                   _replace_fvar_with_bvar(e.body, name, target_bvar_idx + 1))
    return e


def _contains_fvar(e: Expr, name: str) -> bool:
    if isinstance(e, FVar): return e.name == name
    if isinstance(e, (Sort, BVar, Const, Meta)): return False
    if isinstance(e, App): return _contains_fvar(e.fn, name) or _contains_fvar(e.arg, name)
    if isinstance(e, (Lam, Pi)): return _contains_fvar(e.dom, name) or _contains_fvar(e.body, name)
    if isinstance(e, Let): return any(_contains_fvar(c, name) for c in (e.type_, e.value, e.body))
    return False


def _compile_match(scrutinee: Expr, result_ty: Expr,
                   arms: List[Tuple[str, List[str], Expr]],
                   env=None,
                   lvl_params: Tuple[str, ...] = (),
                   bvar_stack: Optional[List[str]] = None,
                   rec_name: Optional[str] = None,
                   scrut_ty_hint: Optional[Expr] = None,
                   rec_arg_pos: int = -1,
                   motive_override: Optional[Expr] = None) -> Expr:
    """Compile a `match` to a recursor application.

    Without env: Nat and Bool only.
    With env:  also polymorphic non-indexed inductives whose parameters can
               be extracted from the scrutinee's type via the kernel.

    When motive_override is given, the fast paths are skipped and the
    user-supplied motive is used directly — enabling dependent matches
    where each arm's result type can mention the scrutinee.
    """
    from .expr import shift as _se
    ctor_names = {c[0] for c in arms}
    Nat = Const("Nat", ())
    Bool = Const("Bool", ())
    one = LSucc(LZero())
    # Bool (non-dependent only)
    if motive_override is None and ctor_names <= {"Bool.true", "Bool.false"}:
        rhs_false = rhs_true = None
        for c, _, r in arms:
            if c == "Bool.false": rhs_false = r
            elif c == "Bool.true": rhs_true = r
        if rhs_false is None or rhs_true is None:
            raise SyntaxError("incomplete Bool match")
        motive = Lam("_", Bool, result_ty)
        return App(App(App(App(Const("Bool.rec", (one,)), motive),
                            rhs_false), rhs_true),
                   scrutinee)
    # Nat (non-dependent only)
    if motive_override is None and ctor_names <= {"Nat.zero", "Nat.succ"}:
        rhs_zero = None
        succ_var = None; rhs_succ = None
        for c, vs, r in arms:
            if c == "Nat.zero":
                rhs_zero = r
            elif c == "Nat.succ":
                if len(vs) != 1:
                    raise SyntaxError("Nat.succ takes one field")
                succ_var = vs[0]
                rhs_succ = r
        if rhs_zero is None or rhs_succ is None:
            raise SyntaxError("incomplete Nat match")
        motive = Lam("_", Nat, result_ty)
        # Structural recursion: if a rec_name was supplied, rewrite
        # `App(Const(rec_name, _), BVar(0))` (=  `rec_name (succ_var)`)
        # in rhs_succ to a sentinel FVar, then later substitute with
        # the IH BVar.
        SENT = "__rec_ih__"
        used_rec = False
        if rec_name is not None:
            rhs_succ_new = _replace_rec_call(rhs_succ, rec_name, 0, SENT, rec_arg_pos)
            used_rec = (rhs_succ_new is not rhs_succ) or \
                       (_contains_fvar(rhs_succ_new, SENT))
            rhs_succ = rhs_succ_new
        rhs_succ_s = _se(rhs_succ, 1, 0)
        result_ty_inside_var = _se(result_ty, 1, 0)
        # In the minor body (inside λ succ_var. λ _ih.), the IH is BVar(0).
        # Replace the sentinel with BVar(0).
        if used_rec:
            rhs_succ_s = _replace_fvar_with_bvar(rhs_succ_s, SENT, 0)
        minor_succ = Lam(succ_var, Nat,
                         Lam("_ih", result_ty_inside_var, rhs_succ_s))
        return App(App(App(App(Const("Nat.rec", (one,)), motive),
                            rhs_zero), minor_succ),
                   scrutinee)
    # ---- general case (requires env) ----
    if env is None:
        raise SyntaxError(f"unsupported match patterns: {ctor_names}")

    # look up the inductive via the first ctor
    first_ctor_name = arms[0][0]
    if not env.has(first_ctor_name):
        raise SyntaxError(f"unknown constructor {first_ctor_name}")
    ctor_decl = env.get(first_ctor_name)
    from .env import Constructor, Inductive, Recursor
    if not isinstance(ctor_decl, Constructor):
        raise SyntaxError(f"{first_ctor_name} is not a constructor")
    ind_name = ctor_decl.inductive
    ind_decl = env.get(ind_name)
    rec_decl = env.get(ind_decl.recursor_name)

    if ind_decl.num_indices > 0:
        if motive_override is None:
            raise SyntaxError(
                f"match on indexed inductive {ind_name} requires "
                f"(motive := ...)")
        # No-recursive-fields check: indexed recursors with rec-args
        # need indices for each rec call too, which the current minor
        # builder doesn't supply.
        for cn in ind_decl.constructor_names:
            cd = env.get(cn)
            r = next((rule for rule in rec_decl.rules
                      if rule.ctor_name == cn), None)
            if r is not None and r.rec_arg_positions:
                raise SyntaxError(
                    f"match on indexed inductive {ind_name} with "
                    f"recursive ctor {cn} not yet supported (use the "
                    f"recursor directly)")

    # Determine the scrutinee's type: prefer the hint (from the
    # surrounding def's binder annotation) over running the kernel,
    # which doesn't handle BVar-containing scrutinees.
    from .kernel import Kernel, LocalCtx
    ker = Kernel(env)
    if scrut_ty_hint is not None:
        scrut_ty = scrut_ty_hint
    else:
        from .expr import BVar as _BV
        def _has_bvar(e):
            if isinstance(e, _BV): return True
            if isinstance(e, (Sort, Const, FVar, Meta)): return False
            if isinstance(e, (App,)): return _has_bvar(e.fn) or _has_bvar(e.arg)
            if isinstance(e, (Lam, Pi)): return _has_bvar(e.dom) or _has_bvar(e.body)
            return False
        if _has_bvar(scrutinee):
            raise SyntaxError(
                "match scrutinee must be closed (no outer-binder references), "
                "or be a top-level match on a def's argument")
        scrut_ty, _ = ker.infer(scrutinee, LocalCtx())
    scrut_ty = ker.whnf(scrut_ty, LocalCtx())
    spine_args: List[Expr] = []
    head_e = scrut_ty
    while isinstance(head_e, App):
        spine_args.insert(0, head_e.arg)
        head_e = head_e.fn
    if not isinstance(head_e, Const) or head_e.name != ind_name:
        raise SyntaxError(
            f"scrutinee type {head_e} doesn't match inductive {ind_name}")
    param_args = spine_args[:ind_decl.num_params]
    index_args = spine_args[ind_decl.num_params:
                            ind_decl.num_params + ind_decl.num_indices]
    ind_lvls = head_e.levels

    # Build motive: when the user supplied one, use it directly; otherwise
    # synthesise the non-dependent λ _ : (ind_name lvls) params..., result_ty.
    ind_applied = Const(ind_name, ind_lvls)
    for pa in param_args:
        ind_applied = App(ind_applied, pa)
    if motive_override is not None:
        motive = motive_override
    else:
        motive = Lam("_", ind_applied, _se(result_ty, 1))

    # Build minors in ctor declaration order
    minors: List[Expr] = []
    for ctor_name in ind_decl.constructor_names:
        # find this ctor's arm
        arm = next((a for a in arms if a[0] == ctor_name), None)
        if arm is None:
            raise SyntaxError(f"missing match arm for {ctor_name}")
        _, vs, rhs = arm
        cd = env.get(ctor_name)
        if len(vs) != cd.num_fields:
            raise SyntaxError(
                f"{ctor_name}: pattern has {len(vs)} vars, "
                f"expected {cd.num_fields}")
        rec_rule_for_this = next(
            (r for r in rec_decl.rules if r.ctor_name == ctor_name), None)
        # Structural recursion: rewrite recursive calls in rhs to sentinel
        # FVars, one per recursive field.  Substituted to the right IH
        # BVar after the minor is assembled.
        SENT_BASE = "__rec_ih_"
        rec_sentinels: List[str] = []
        if (rec_name is not None and rec_rule_for_this is not None
                and rec_rule_for_this.rec_arg_positions):
            for k, p in enumerate(rec_rule_for_this.rec_arg_positions):
                target_idx = cd.num_fields - 1 - p
                sent_name = f"{SENT_BASE}{k}"
                rhs = _replace_rec_call(rhs, rec_name, target_idx, sent_name, rec_arg_pos)
                rec_sentinels.append(sent_name)
        # The minor's expected shape:
        #   λ f_0:F_0. ... λ f_{k-1}:F_{k-1}.
        #     λ r_0:M(f_{rec_pos_0}). ... λ r_{m-1}:M(f_{rec_pos_{m-1}}).
        #       rhs_for_this_ctor
        ctor_ty = cd.type_
        # skip params
        for _ in range(cd.num_params):
            if not isinstance(ctor_ty, Pi):
                raise SyntaxError("malformed ctor type")
            ctor_ty = subst_bvar_top(ctor_ty.body, param_args[_])  # not quite — see below
        # the above is awkward; let's just inst_levels then peel params
        # We'll opt for a simpler simulation: extract field types by
        # peeling Pi's, performing param substitution on the fly.
        field_types: List[Expr] = []
        from .expr import inst_levels as _inst, subst_bvar as _sb
        ct = cd.type_
        ct = _inst(ct, cd.level_params, ind_lvls)
        for pa in param_args:
            if not isinstance(ct, Pi):
                raise SyntaxError("bad ctor shape")
            ct = _sb(ct.body, 0, pa)
        # now ct is Π fields..., Ind params
        for j in range(cd.num_fields):
            if not isinstance(ct, Pi):
                raise SyntaxError("bad ctor shape")
            field_types.append(ct.dom)
            # to descend, substitute BVar 0 with a dummy (we just need
            # field types' shapes, not the residual)
            ct = ct.body
        # rec positions: recover from the rule (matching ctor) on rec_decl
        rec_rule = next((r for r in rec_decl.rules if r.ctor_name == ctor_name), None)
        rec_positions = rec_rule.rec_arg_positions if rec_rule else ()
        # Build minor body inside-out.
        # rhs was parsed with bvar_stack + vs (vs are field names; BVars
        # in rhs index: BVar(0)=last field, BVar(1)=prev, etc., then outer)
        # Inside the minor we add fields + IH binders.  We then re-shift rhs
        # to account for the IH binders added below.
        n_rec = len(rec_positions)
        minor_body = _se(rhs, n_rec, 0)
        # Substitute each rec-call sentinel FVar with its IH BVar now,
        # BEFORE wrapping (so target_bvar indices are interpreted at the
        # deepest body's scope and the wrap-time increments are correct).
        if rec_sentinels:
            for k, sent_name in enumerate(rec_sentinels):
                ih_bvar_idx = n_rec - 1 - k
                minor_body = _replace_fvar_with_bvar(
                    minor_body, sent_name, ih_bvar_idx)
        # wrap IH binders (innermost first): r_{n-1}, ..., r_0
        # IH type for r_k = motive (field_{rec_positions[k]})
        # When we're about to wrap r_k, the inner body has (n_rec - 1 - k) r-binders below.
        # field_p sits at BVar( (n_rec - 1 - k) + (n_fields - 1 - p) )
        # motive applied to that field gives the IH type.
        n_fields = cd.num_fields
        for k in reversed(range(n_rec)):
            p = rec_positions[k]
            depth_to_field = (n_rec - 1 - k) + (n_fields - 1 - p)
            ih_ty = App(_se(motive, n_rec - 1 - k + n_fields, 0),
                        BVar(depth_to_field))
            minor_body = Lam(f"r{k}", ih_ty, minor_body)
        # wrap field binders.  field_types[j] was extracted from the
        # already-peeled ctor type (each iter goes one binder deeper into
        # the Pi chain), so it's at the right depth already — no shift.
        for j in reversed(range(n_fields)):
            minor_body = Lam(vs[j], field_types[j], minor_body)
        minors.append(minor_body)

    # Build recursor application.  Leave ALL level args empty so the
    # elaborator auto-instantiates fresh level metas; they'll be solved
    # by unification with the inductive's args (gives ind_lvls) and with
    # the motive's body (gives the motive universe).
    rec_head = Const(rec_decl.name, ())
    for pa in param_args:
        rec_head = App(rec_head, pa)
    rec_head = App(rec_head, motive)
    for mn in minors:
        rec_head = App(rec_head, mn)
    for ia in index_args:
        rec_head = App(rec_head, ia)
    rec_head = App(rec_head, scrutinee)
    return rec_head


def subst_bvar_top(e, v):
    from .expr import subst_bvar
    return subst_bvar(e, 0, v)


def parse_program(src: str, env=None):
    toks = lex(src)
    p = P(toks, src, env)
    return p.parse_program()


# --------------- elaboration to env ---------------

def elaborate(src: str, env: Env) -> List[str]:
    """Parse and add to env incrementally — each declaration becomes part
    of env as soon as it is parsed, so later declarations' `match`-style
    elaboration and implicit-arg inference can inspect it."""
    from .elaborator import elaborate_decl
    toks = lex(src)
    p = P(toks, src, env)
    added: List[str] = []
    while p.peek() is not None:
        decl = p.parse_decl()
        kind = decl[0]
        before = list(env.order)
        if kind == "inductive":
            _, name, lvl_params, params, result_ty, ctors = decl
            elaborate_decl(env, "inductive", name, lvl_params,
                           params=params, result_ty=result_ty, ctors=ctors)
        elif kind == "structure":
            _, name, lvl_params, params, result_ty, fields, is_class = decl
            elaborate_decl(env, "structure", name, lvl_params,
                           params=params, result_ty=result_ty,
                           fields=fields, is_class=is_class)
        elif kind == "infix":
            # decl is ("infix", op_text, (), [], None, [func_name, prec, assoc])
            op_text = decl[1]
            func_name, prec, assoc = decl[5]
            p.infix_table[op_text] = (prec, assoc, func_name)
            continue                                  # don't add to env
        else:
            _, name, lvl_params, binders, ty, body = decl
            elaborate_decl(env, kind, name, lvl_params, ty, body)
        added.extend(d for d in env.order if d not in before)
    return added
