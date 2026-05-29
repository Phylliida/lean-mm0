"""A minimal MM0-style proof verifier.

This is the **trusted base** of the project.  Keep it small, simple,
and auditable.

Source format (s-expressions, one declaration per top-level form):

    (sort NAME)
      Declare a new sort.

    (term NAME ((arg1 SORT1) (arg2 SORT2) ...) RESULT-SORT)
      Declare a term constructor (pure, no reduction).

    (def NAME ((arg1 SORT1) ...) RESULT-SORT BODY)
      Declare a definitional rewrite rule:  (NAME arg1 ...) reduces to BODY.

    (builtin NAME ((arg1 SORT1) ...) RESULT-SORT)
      Declare a function whose reduction is hard-coded in this file
      (used for `shift` and `subst1`, which would be unwieldy in MM0).

    (axiom NAME ((var1 SORT1) ...) (HYP1 HYP2 ...) CONCL)
      Universally-quantified axiom with hypotheses and conclusion.

    (theorem NAME ((var1 SORT1) ...) (HYP1 HYP2 ...) CONCL PROOF)
      Theorem with a forward proof.

A PROOF is one of:

    (apply NAME (TERM_FOR_VAR1 TERM_FOR_VAR2 ...) (PROOF_FOR_HYP1 ...))
    (hyp K)            -- the K-th hypothesis of the surrounding theorem

Equality of conclusions modulo:
  * α-equivalence (we use de Bruijn so this is syntactic)
  * δ-reduction through (def ...) declarations
  * builtin reductions (`shift`, `subst1`)

The verifier evaluates terms to canonical normal form before comparing.
This is the only "decidable equality" baked into the trusted core.
"""
from __future__ import annotations
from dataclasses import dataclass, field
from typing import List, Tuple, Dict, Optional, Union


# -------------------- s-expression parser --------------------

Atom = str
SExpr = Union[Atom, List["SExpr"]]


def parse(text: str) -> List[SExpr]:
    """Parse a sequence of top-level s-expressions."""
    i = 0
    n = len(text)
    out: List[SExpr] = []

    def skip_ws():
        nonlocal i
        while i < n:
            c = text[i]
            if c.isspace():
                i += 1
            elif c == ';':
                # line comment
                while i < n and text[i] != '\n':
                    i += 1
            else:
                return

    def read_sexp() -> SExpr:
        nonlocal i
        skip_ws()
        if i >= n:
            raise SyntaxError("unexpected EOF")
        c = text[i]
        if c == '(':
            i += 1
            items: List[SExpr] = []
            while True:
                skip_ws()
                if i >= n:
                    raise SyntaxError("unbalanced (")
                if text[i] == ')':
                    i += 1
                    return items
                items.append(read_sexp())
        if c == ')':
            raise SyntaxError("unexpected )")
        # atom: read until whitespace or paren
        j = i
        while j < n and not text[j].isspace() and text[j] not in '()':
            j += 1
        atom = text[i:j]
        i = j
        return atom

    while True:
        skip_ws()
        if i >= n:
            break
        out.append(read_sexp())
    return out


def sexp_str(e: SExpr) -> str:
    if isinstance(e, str):
        return e
    return "(" + " ".join(sexp_str(x) for x in e) + ")"


# -------------------- environment --------------------

@dataclass
class TermDecl:
    name: str
    args: List[Tuple[str, str]]      # (arg-name, sort)
    result_sort: str


@dataclass
class DefDecl:
    name: str
    args: List[Tuple[str, str]]
    result_sort: str
    body: SExpr


@dataclass
class OpaqueDefDecl:
    """Like DefDecl, but the body is NOT exposed for δ-reduction during
    normalization.  The body is kept so the (opaque-def-typing NAME PROOF)
    rule can check that a body-of-NAME typing derivation matches.  Used
    for lemma proofs that we want to verify but not unfold at every call
    site — without this distinction, every subsequent lemma re-normalises
    the entire chain of dependent proofs, which is exponentially bad."""
    name: str
    args: List[Tuple[str, str]]
    result_sort: str
    body: SExpr


@dataclass
class BuiltinDecl:
    name: str
    args: List[Tuple[str, str]]
    result_sort: str


@dataclass
class AxiomDecl:
    name: str
    vars: List[Tuple[str, str]]      # (var-name, sort)
    hyps: List[SExpr]
    concl: SExpr


@dataclass
class TheoremDecl:
    name: str
    vars: List[Tuple[str, str]]
    hyps: List[SExpr]
    concl: SExpr
    proof: SExpr


@dataclass
class IotaRule:
    """A computational rule for one (recursor, constructor) pair.

    Spine layout of the recursor application:
       rec  p_0 .. p_{P-1}  m_0 .. m_{M-1}  mn_0 .. mn_{MN-1}  i_0 .. i_{I-1}  major

    Where major is `ctor p_0 .. p_{P-1} f_0 .. f_{F-1}` (constructor params
    match the inductive's params).  After ι:

       RHS = rhs_template with BVar(i) -> env_subst[total-1-i]
       env_subst = params ++ motives ++ minors ++ fields ++ rec_results
       rec_results[k] = rec p_0 .. mn_{MN-1}  i_0 .. i_{I-1}  field_{rec_positions[k]}

    For now we require n_indices == 0 (indices for Eq are handled by a
    separate rule that captures the special "b ≡ a" relation).
    """
    rec_name: str
    ctor_name: str
    n_params: int
    n_motives: int
    n_minors: int
    n_indices: int
    n_fields: int
    rec_positions: Tuple[int, ...]
    rhs_template: SExpr
    # For each recursive position, a tuple of n_indices index expressions
    # describing the indices used for the recursive call.  The expressions
    # use BVars in the env_subst convention up to (but excluding) rec_results.
    rec_index_templates: Tuple[Tuple[SExpr, ...], ...] = ()
    # For most recursors n_ctor_params == n_params.  For Quot.lift the
    # ctor (Quot.mk) carries fewer params than the recursor's leading args
    # (which include β); set this lower than n_params in that case.
    n_ctor_params: Optional[int] = None


@dataclass
class VerifierEnv:
    sorts: Dict[str, None] = field(default_factory=dict)
    terms: Dict[str, TermDecl] = field(default_factory=dict)
    defs: Dict[str, DefDecl] = field(default_factory=dict)
    opaque_defs: Dict[str, OpaqueDefDecl] = field(default_factory=dict)
    builtins: Dict[str, BuiltinDecl] = field(default_factory=dict)
    axioms: Dict[str, AxiomDecl] = field(default_factory=dict)
    theorems: Dict[str, TheoremDecl] = field(default_factory=dict)
    # iota_rules[rec_name][ctor_name] = IotaRule
    iota_rules: Dict[str, Dict[str, IotaRule]] = field(default_factory=dict)
    # the structural shape of a recursor (so we know its spine length even
    # before we have an actual rule firing).  rec_name -> (P,M,MN,I)
    recursor_shape: Dict[str, Tuple[int, int, int, int]] = field(default_factory=dict)


# -------------------- term normalization --------------------

class VerifyError(Exception):
    pass


def _is_var(e: SExpr, var_names: set) -> bool:
    return isinstance(e, str) and e in var_names


def _subst(e: SExpr, sigma: Dict[str, SExpr]) -> SExpr:
    if isinstance(e, str):
        return sigma.get(e, e)
    return [_subst(x, sigma) for x in e]


def _normalize(e: SExpr, env: VerifierEnv, fuel: int = 200_000) -> SExpr:
    """Reduce e by:
       - δ-expansion of `def` declarations,
       - execution of `builtin`s,
       - β-reduction:  (eapp (elam A b) a)  →  subst1 b a,
       - ζ-reduction:  (elet T v b)         →  subst1 b v.

    All innermost-first.  Equality between MM0 terms is decided after
    normalisation, so this set of reductions defines the trusted
    definitional-equality relation."""
    if fuel <= 0:
        raise VerifyError("normalization fuel exhausted")
    if isinstance(e, str):
        # opaque constant: try to δ-expand 0-ary defs
        if e in env.defs and len(env.defs[e].args) == 0:
            return _normalize(env.defs[e].body, env, fuel - 1)
        return e
    if len(e) == 0:
        return e
    head = e[0]
    norm_args = [_normalize(a, env, fuel - 1) for a in e[1:]]
    if isinstance(head, str):
        if head in env.defs:
            d = env.defs[head]
            if len(norm_args) != len(d.args):
                raise VerifyError(f"def {head} arity mismatch")
            sigma = {a[0]: v for a, v in zip(d.args, norm_args)}
            return _normalize(_subst(d.body, sigma), env, fuel - 1)
        if head in env.builtins:
            return _normalize(_exec_builtin(head, norm_args, env), env, fuel - 1)
        # β-reduction:  (eapp (elam A b) a)
        if head == "eapp" and len(norm_args) == 2 \
           and isinstance(norm_args[0], list) and len(norm_args[0]) == 3 \
           and norm_args[0][0] == "elam":
            _, _A, b = norm_args[0]
            a = norm_args[1]
            return _normalize(_subst1(b, a, 0), env, fuel - 1)
        # ι-reduction: recursor application
        if head == "eapp" and len(norm_args) == 2:
            spine = [["eapp"] + norm_args]  # placeholder, we'll uncurry properly
            iota_red = _try_iota(["eapp"] + norm_args, env, fuel - 1)
            if iota_red is not None:
                return iota_red
        # ζ-reduction:  (elet T v b)
        if head == "elet" and len(norm_args) == 3:
            _T, v, b = norm_args
            return _normalize(_subst1(b, v, 0), env, fuel - 1)
        # level normalisation:  (limax a lzero) = lzero,  (limax a (lsucc _)) = (lmax a _), etc.
        if head == "limax" and len(norm_args) == 2:
            a, b = norm_args
            if b == "lzero":
                return "lzero"
            if isinstance(b, list) and len(b) == 2 and b[0] == "lsucc":
                return _normalize(["lmax", a, b], env, fuel - 1)
            return [head] + norm_args
        if head == "lmax" and len(norm_args) == 2:
            a, b = norm_args
            if a == "lzero":
                return b
            if b == "lzero":
                return a
            if _eq(a, b):
                return a
            return [head] + norm_args
    return [head] + norm_args


def _uncurry(e: SExpr) -> Tuple[SExpr, List[SExpr]]:
    """Decompose an (eapp ... ) chain into (head, [arg0, arg1, ...])."""
    # Build in reverse (O(n) appends) and reverse once at the end
    # rather than `args.insert(0, …)` which is O(n²).  In practice
    # spine length is small so this is a cleanup, not a measurable
    # speedup — but the algorithmic version is plainly more correct.
    args: List[SExpr] = []
    while isinstance(e, list) and len(e) == 3 and e[0] == "eapp":
        args.append(e[2])
        e = e[1]
    args.reverse()
    return e, args


def _curry(head: SExpr, args: List[SExpr]) -> SExpr:
    e: SExpr = head
    for a in args:
        e = ["eapp", e, a]
    return e


def _try_iota(e: SExpr, env: VerifierEnv, fuel: int) -> Optional[SExpr]:
    """If e is a recursor application of the right shape over a constructor
    major, fire the corresponding ι rule.  Otherwise return None."""
    head, args = _uncurry(e)
    if not isinstance(head, str):
        return None
    shape = env.recursor_shape.get(head)
    if shape is None:
        return None
    n_params, n_motives, n_minors, n_indices = shape
    total_needed = n_params + n_motives + n_minors + n_indices + 1
    if len(args) < total_needed:
        return None
    major_idx = n_params + n_motives + n_minors + n_indices
    major = _normalize(args[major_idx], env, fuel - 1)
    m_head, m_args = _uncurry(major)
    if not isinstance(m_head, str):
        return None
    rules = env.iota_rules.get(head, {})
    rule = rules.get(m_head)
    if rule is None:
        return None
    n_ctor_params = rule.n_ctor_params if rule.n_ctor_params is not None else n_params
    if len(m_args) < n_ctor_params + rule.n_fields:
        return None
    # The ctor's fields come after the ctor's params in m_args.
    field_args = m_args[n_ctor_params:n_ctor_params + rule.n_fields]
    # env_subst uses the *recursor*'s params (which may include extras like
    # β for Quot.lift), NOT the ctor's params.
    rec_params_args = args[:n_params]
    motives_args = args[n_params:n_params + n_motives]
    minors_args = args[n_params + n_motives:n_params + n_motives + n_minors]
    indices_args = args[n_params + n_motives + n_minors:major_idx]
    # build rec_results.  For indexed inductives, each recursive call's
    # indices come from the constructor's structure (via index templates)
    # rather than the outer indices_args.
    rec_results: List[SExpr] = []
    env_no_rec = list(rec_params_args) + list(motives_args) + list(minors_args) \
               + list(field_args)
    for k, pos in enumerate(rule.rec_positions):
        sub_major = field_args[pos]
        if rule.n_indices == 0:
            sub_indices: List[SExpr] = []
        else:
            tpl = rule.rec_index_templates[k] if k < len(rule.rec_index_templates) else ()
            if len(tpl) != rule.n_indices:
                raise VerifyError(
                    f"iota for {rule.rec_name}/{rule.ctor_name}: "
                    f"rec_index_templates[{k}] has {len(tpl)} entries, "
                    f"expected {rule.n_indices}")
            sub_indices = [_instantiate_template(t, env_no_rec, env)
                           for t in tpl]
        prefix = rec_params_args + motives_args + minors_args + sub_indices
        rec_call = _curry(head, prefix + [sub_major])
        rec_results.append(rec_call)
    env_subst = env_no_rec + list(rec_results)
    # apply rhs template
    rhs = _instantiate_template(rule.rhs_template, env_subst, env)
    # also append any extra args beyond `total_needed`
    extra = args[total_needed:]
    if extra:
        rhs = _curry(rhs, extra)
    return _normalize(rhs, env, fuel - 1)


def _instantiate_template(template: SExpr, env_subst: List[SExpr],
                          env: VerifierEnv, depth: int = 0) -> SExpr:
    """Walk the template; replace evar references that correspond to
    env_subst entries with the values, shifting as needed."""
    n = len(env_subst)
    if isinstance(template, str):
        return template
    if len(template) == 0:
        return template
    head = template[0]
    if head == "evar":
        idx = _to_int(template[1])
        if idx < depth:
            return template
        pos = n - 1 - (idx - depth)
        if 0 <= pos < n:
            v = env_subst[pos]
            return _shift(v, depth, 0)
        # ran past env; leave as-is shifted down
        return ["evar", _from_int(idx - n)]
    # binders increase depth
    if head in ("elam", "epi"):
        return [head,
                _instantiate_template(template[1], env_subst, env, depth),
                _instantiate_template(template[2], env_subst, env, depth + 1)]
    if head == "elet":
        return [head,
                _instantiate_template(template[1], env_subst, env, depth),
                _instantiate_template(template[2], env_subst, env, depth),
                _instantiate_template(template[3], env_subst, env, depth + 1)]
    return [head] + [_instantiate_template(a, env_subst, env, depth)
                     for a in template[1:]]


def _exec_builtin(name: str, args: List[SExpr], env: VerifierEnv) -> SExpr:
    """Built-in computational rules for CIC syntax manipulation.
    These are the only term-level reductions hardcoded into the verifier.
    Kept small and obviously correct."""
    if name == "shift":
        # (shift e d c)   shift de Bruijn indices ≥ c in e by d
        e, d, c = args
        return _shift(e, _to_int(d), _to_int(c))
    if name == "subst1":
        # (subst1 body v)   substitute v for BVar 0 in body
        body, v = args
        return _subst1(body, v, 0)
    if name == "shift1":
        # convenience: shift by 1
        e, = args
        return _shift(e, 1, 0)
    if name == "lvl-pred":
        # (lvl-pred l)  : the level constructor of the type of `l`'s value;
        #                 used by ht-sort, equals (lsucc l)
        l, = args
        return ["lsucc", l]
    raise VerifyError(f"unknown builtin: {name}")


def _to_int(e: SExpr) -> int:
    n = 0
    while isinstance(e, list) and len(e) == 2 and e[0] == "nsucc":
        n += 1
        e = e[1]
    if e == "nzero" or e == ["nzero"]:
        return n
    raise VerifyError(f"not a nat literal: {sexp_str(e)}")


def _from_int(n: int) -> SExpr:
    e: SExpr = "nzero"
    for _ in range(n):
        e = ["nsucc", e]
    return e


def _shift(e: SExpr, d: int, c: int) -> SExpr:
    """Mirror src.expr.shift for the s-expression representation."""
    if isinstance(e, str):
        return e
    if len(e) == 0:
        return e
    head = e[0]
    if head == "evar":
        idx = _to_int(e[1])
        new_idx = idx + d if idx >= c else idx
        return ["evar", _from_int(new_idx)]
    if head in ("esort", "econst"):
        return e
    if head == "eapp":
        return ["eapp", _shift(e[1], d, c), _shift(e[2], d, c)]
    if head == "elam":
        return ["elam", _shift(e[1], d, c), _shift(e[2], d, c + 1)]
    if head == "epi":
        return ["epi", _shift(e[1], d, c), _shift(e[2], d, c + 1)]
    if head == "elet":
        return ["elet", _shift(e[1], d, c), _shift(e[2], d, c),
                _shift(e[3], d, c + 1)]
    # opaque constructor: shift inside each arg conservatively (do nothing
    # for non-expr args).  For sample prelude this only matters for expr.
    return [head] + [_shift(a, d, c) for a in e[1:]]


def _subst1(e: SExpr, v: SExpr, j: int) -> SExpr:
    """Substitute v for BVar j in e; mirrors src.expr.subst_bvar."""
    if isinstance(e, str):
        return e
    head = e[0]
    if head == "evar":
        idx = _to_int(e[1])
        if idx == j:
            return _shift(v, j, 0)
        if idx > j:
            return ["evar", _from_int(idx - 1)]
        return e
    if head in ("esort", "econst"):
        return e
    if head == "eapp":
        return ["eapp", _subst1(e[1], v, j), _subst1(e[2], v, j)]
    if head == "elam":
        return ["elam", _subst1(e[1], v, j), _subst1(e[2], v, j + 1)]
    if head == "epi":
        return ["epi", _subst1(e[1], v, j), _subst1(e[2], v, j + 1)]
    if head == "elet":
        return ["elet", _subst1(e[1], v, j), _subst1(e[2], v, j),
                _subst1(e[3], v, j + 1)]
    return [head] + [_subst1(a, v, j) for a in e[1:]]


def _equal(a: SExpr, b: SExpr, env: VerifierEnv) -> bool:
    a = _normalize(a, env)
    b = _normalize(b, env)
    return _eq(a, b)


def _eq(a: SExpr, b: SExpr) -> bool:
    if isinstance(a, str) and isinstance(b, str):
        return a == b
    if isinstance(a, list) and isinstance(b, list):
        if len(a) != len(b):
            return False
        return all(_eq(x, y) for x, y in zip(a, b))
    return False


# -------------------- declaration processing --------------------

def add_decl(env: VerifierEnv, decl: SExpr) -> None:
    if not isinstance(decl, list) or len(decl) == 0:
        raise VerifyError(f"bad decl: {decl}")
    head = decl[0]
    if head == "sort":
        _, name = decl
        if name in env.sorts:
            raise VerifyError(f"duplicate sort {name}")
        env.sorts[name] = None
    elif head == "term":
        _, name, args, result_sort = decl
        arg_pairs = [(a[0], a[1]) for a in args]
        env.terms[name] = TermDecl(name, arg_pairs, result_sort)
    elif head == "def":
        _, name, args, result_sort, body = decl
        arg_pairs = [(a[0], a[1]) for a in args]
        env.defs[name] = DefDecl(name, arg_pairs, result_sort, body)
    elif head == "opaque-def":
        _, name, args, result_sort, body = decl
        arg_pairs = [(a[0], a[1]) for a in args]
        env.opaque_defs[name] = OpaqueDefDecl(name, arg_pairs, result_sort, body)
    elif head == "builtin":
        _, name, args, result_sort = decl
        arg_pairs = [(a[0], a[1]) for a in args]
        env.builtins[name] = BuiltinDecl(name, arg_pairs, result_sort)
    elif head == "iota":
        # (iota REC-NAME CTOR-NAME N-PARAMS N-MOTIVES N-MINORS N-INDICES
        #       N-FIELDS (REC-POSITIONS) RHS-TEMPLATE)
        # Optional 10th element: ((idx-tpl-for-rec0...) (idx-tpl-for-rec1...) ...)
        # 10 args: no index templates, no explicit ctor_params
        # 11 args: include index templates
        # 12 args: include index templates and n_ctor_params
        idx_tpls: List[Tuple[SExpr, ...]] = []
        n_ctor_params_opt: Optional[int] = None
        if len(decl) == 10:
            _, rec_name, ctor_name, np, nm, nmn, ni, nf, rec_pos, rhs = decl
        elif len(decl) == 11:
            (_, rec_name, ctor_name, np, nm, nmn, ni, nf,
             rec_pos, rhs, idx_tpls_raw) = decl
            idx_tpls = [tuple(t) for t in idx_tpls_raw]
        elif len(decl) == 12:
            (_, rec_name, ctor_name, np, nm, nmn, ni, nf,
             rec_pos, rhs, idx_tpls_raw, ncp) = decl
            idx_tpls = [tuple(t) for t in idx_tpls_raw]
            n_ctor_params_opt = int(ncp)
        else:
            raise VerifyError(f"bad iota declaration arity: {len(decl)}")
        rule = IotaRule(
            rec_name=rec_name,
            ctor_name=ctor_name,
            n_params=int(np),
            n_motives=int(nm),
            n_minors=int(nmn),
            n_indices=int(ni),
            n_fields=int(nf),
            rec_positions=tuple(int(x) for x in rec_pos),
            rhs_template=rhs,
            rec_index_templates=tuple(idx_tpls),
            n_ctor_params=n_ctor_params_opt,
        )
        env.iota_rules.setdefault(rec_name, {})[ctor_name] = rule
        shape = (rule.n_params, rule.n_motives, rule.n_minors, rule.n_indices)
        existing = env.recursor_shape.get(rec_name)
        if existing is not None and existing != shape:
            raise VerifyError(f"inconsistent recursor shape for {rec_name}: "
                              f"{existing} vs {shape}")
        env.recursor_shape[rec_name] = shape
    elif head == "axiom":
        _, name, vars_, hyps, concl = decl
        var_pairs = [(v[0], v[1]) for v in vars_]
        env.axioms[name] = AxiomDecl(name, var_pairs, hyps, concl)
    elif head == "theorem":
        _, name, vars_, hyps, concl, proof = decl
        var_pairs = [(v[0], v[1]) for v in vars_]
        # verify the proof
        verify_proof(env, var_pairs, hyps, concl, proof)
        # register as a theorem (usable for later proofs)
        env.theorems[name] = TheoremDecl(name, var_pairs, hyps, concl, proof)
    else:
        raise VerifyError(f"unknown declaration head: {head}")


# -------------------- proof checker --------------------

def verify_proof(env: VerifierEnv,
                 vars_: List[Tuple[str, str]],
                 hyps: List[SExpr],
                 concl: SExpr,
                 proof: SExpr) -> None:
    var_set = {v for v, _ in vars_}
    got = _check_proof(env, proof, hyps, var_set)
    if not _equal(got, concl, env):
        raise VerifyError(
            f"proof concludes {sexp_str(got)},\n  expected {sexp_str(concl)}"
        )


def _check_proof(env: VerifierEnv, proof: SExpr,
                 hyps: List[SExpr], var_set: set) -> SExpr:
    if not isinstance(proof, list) or len(proof) == 0:
        raise VerifyError(f"bad proof: {proof}")
    head = proof[0]
    if head == "hyp":
        _, k = proof
        idx = int(k)
        if idx < 0 or idx >= len(hyps):
            raise VerifyError(f"hyp index out of range: {idx}")
        return hyps[idx]
    if head == "opaque-def-typing":
        # (opaque-def-typing OPAQUE-NAME BODY-PROOF)
        # BODY-PROOF must conclude (has-type G <body> T) where <body> is the
        # opaque def's stored body.  Result: (has-type G OPAQUE-NAME T).
        _, opaque_name, body_proof = proof
        if opaque_name not in env.opaque_defs:
            raise VerifyError(
                f"opaque-def-typing: {opaque_name} is not an opaque-def")
        body_concl = _check_proof(env, body_proof, hyps, var_set)
        if not (isinstance(body_concl, list) and len(body_concl) == 4
                and body_concl[0] == "has-type"):
            raise VerifyError(
                f"opaque-def-typing: inner proof must conclude (has-type G e T), "
                f"got {sexp_str(body_concl)}")
        _, G, body_term, T = body_concl
        expected_body = env.opaque_defs[opaque_name].body
        if not _equal(body_term, expected_body, env):
            raise VerifyError(
                f"opaque-def-typing: inner proof's subject does not match "
                f"opaque body.\n  expected: {sexp_str(_normalize(expected_body, env))}"
                f"\n  got: {sexp_str(_normalize(body_term, env))}")
        return ["has-type", G, opaque_name, T]
    if head == "apply":
        _, name, sigma_list, sub_proofs = proof
        ref = env.axioms.get(name) or env.theorems.get(name)
        if ref is None:
            raise VerifyError(f"unknown reference: {name}")
        if len(sigma_list) != len(ref.vars):
            raise VerifyError(
                f"{name}: expected {len(ref.vars)} term args, got {len(sigma_list)}"
            )
        sigma = {v[0]: t for v, t in zip(ref.vars, sigma_list)}
        # check each premise
        if len(sub_proofs) != len(ref.hyps):
            raise VerifyError(
                f"{name}: expected {len(ref.hyps)} subproofs, got {len(sub_proofs)}"
            )
        for h, p in zip(ref.hyps, sub_proofs):
            want = _subst(h, sigma)
            got = _check_proof(env, p, hyps, var_set)
            if not _equal(got, want, env):
                raise VerifyError(
                    f"in {name}: hypothesis mismatch.\n"
                    f"  want: {sexp_str(_normalize(want, env))}\n"
                    f"  got:  {sexp_str(_normalize(got, env))}"
                )
        return _subst(ref.concl, sigma)
    raise VerifyError(f"unknown proof form: {head}")


# -------------------- entry point --------------------

def verify_text(text: str, env: Optional[VerifierEnv] = None) -> VerifierEnv:
    if env is None:
        env = VerifierEnv()
    for decl in parse(text):
        add_decl(env, decl)
    return env


def verify_file(path: str, env: Optional[VerifierEnv] = None) -> VerifierEnv:
    with open(path) as f:
        return verify_text(f.read(), env)


if __name__ == "__main__":
    import sys
    env = VerifierEnv()
    for path in sys.argv[1:]:
        try:
            verify_file(path, env)
            print(f"ok  {path}")
        except VerifyError as e:
            print(f"FAIL  {path}: {e}", file=sys.stderr)
            sys.exit(1)
