# Never-continuation repair regression

This small Rust crate exercises a panic-returning Never call, a recursively
diverging Never call, guarded uses of both calls, and an ordinary returning
function. It is a compiler regression fixture, not a replacement bytes model.

After the normal environment activation, run `python3 scripts/check-never-repair.py`
from the bytes version directory. The checker extracts one LLBC file and runs both
the original pinned Aeneas and the isolated repaired executable on it. It requires
the original Cps.Unit failure, successful complete repaired extraction, no
application axioms/placeholders, and identical output for the ordinary function.
The optional first argument selects the repaired executable; an optional second
argument names a new output directory. Every invocation keeps its logs.

The pass preserves each typed Never-returning call and adds an unreachable
continuation. A successful value of Never cannot reach that continuation. The
separately checked monadic equality covers arbitrary failure, effects and
divergence; it does not formally verify the OCaml implementation of the pass.
The repaired compiler remains part of the recorded translation trust boundary.
The panic branch is not deleted from the extracted bytes implementation.

The fixture uses recursive divergence because direct infinite loops without
breaks encounter a separate unsupported-loop limitation in the fixed Aeneas
baseline. No proof of such loops is claimed by this regression.
