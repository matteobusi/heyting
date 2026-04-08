# Compiler correctness

Reflection the naive way is apparently hard in this setting, so I try to follow the approach from Abate et al. (TRCCCS).

We need to adapt the framework and instantiate it to witnesses and zkps, TrinitaryCC.lean does that, and provides theorems to move from one definition to another.

The current framework in `Core/Pass.lean` uses `PresReflPass` which bundles:
- A `Pass` with `compile` and `witnessRel` (the trace relation)
- `PreservingPass` (forward: source satisfaction implies target satisfaction for a related witness)
- `ReflectingPass` (backward: target satisfaction implies source satisfaction for a related witness)

Both passes (FlatIR→R1CS and StructIR→FlatIR) are proved as `PresReflPass` instances with meaningful witness relations — not `True`.

The trinitarian equivalence (TPσ ↔ CC~ ↔ TPτ) is proved in `Heyting/Core/TrinitaryCC.lean`.

TODO: It would be cool to have builders for instances, i.e., provided a TP^sigma build TP^tau (and viceversa) and the same for CC.
