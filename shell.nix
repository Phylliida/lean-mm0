{ pkgs ? import <nixpkgs> {} }:

pkgs.mkShell {
  name = "lean-mm0-shell";

  buildInputs = with pkgs; [
    pypy3       # PyPy interpreter — for faster test cycles
    python3     # CPython — the canonical interpreter
  ];

  shellHook = ''
    # Set up a PyPy venv with pytest + xdist on first shell entry.
    # The venv lives at .venv/ (gitignored).  We use PyPy as the
    # interpreter because it's the speed win we're after; CPython is
    # still available on PATH as `python3` for comparison.
    if [ ! -d .venv ]; then
      echo "Creating PyPy venv at .venv/..."
      pypy3 -m venv .venv
      .venv/bin/pip install --quiet --upgrade pip
      .venv/bin/pip install --quiet pytest pytest-xdist
      echo "  done."
    fi

    echo ""
    echo "lean-mm0 dev shell ready.  Run tests with:"
    echo "  .venv/bin/pytest tests/ -n auto      # PyPy + xdist"
    echo "  python3   -m pytest tests/ -n auto   # CPython + xdist"
    echo ""
  '';
}
