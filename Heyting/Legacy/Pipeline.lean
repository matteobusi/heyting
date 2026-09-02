/-
Copyright (c) 2025 Heyting Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Heyting.Passes.Pipeline

/-!
# Legacy StructIR compiler pipeline

Canonical import boundary for the reference pipeline:

```text
StructIR → FlatIR → FlatIR(compact) → R1CS
```

The implementation remains verified and executable, but is intentionally
isolated under `Legacy.Pipeline`. New compiler architecture should target the
dialect pipeline instead of adding more StructIR-specific stages here.
-/
