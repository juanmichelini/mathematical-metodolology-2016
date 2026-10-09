# Legacy modules

These files are earlier iterations and sketches. They are **not** used by `Main`, `Test`, or any of the modules behind the thesis results (`Syntax`, `Util`, `Type`, `Compute`, `Prove`, `Propose`, `PrettyPrint`), and they are not built by CI.

- `Strategy.hs`: a design sketch. It imports `Prueba.Bool` and `Prueba.Nat` (not in the repo) and has signatures without definitions, so it does not compile.
- `Tactic.hs`, `TacticObjs.hs`, `TacticMaybe.hs`: older versions of the tactics, superseded by `Prove.hs`. `Tactic.hs` and `TacticObjs.hs` both declare `module Tactic`, so they cannot be built together.
- `SimpleSubst.hs`, `Misc.hs`: helpers used only by the files above.

Kept for history. See issue #2.
