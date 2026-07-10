import Scott1982.Proposition62
import Scott1982.Factoid65
import Scott1982.FunctionSpace
-- Stretch goal will also need Theorem 7.2 and Mathlib.CategoryTheory.

/-!
# Factoid 7.7 — cartesian closed structure (stretch goal)

**Scott 1982 (*Categories again*, after the combinators).** The technical term for what
Props 6.2 and Theorem 7.2 show of the category of information systems and approximable
mappings is *cartesian closed category*. Scott declines to develop the categorical
packaging in the paper (“without going into details”).

**Stretch goal.** After Theorem 7.2 lands, package the concrete data
(Prop 6.2 products, Thm 7.2 exponentials / `apply`–`curry`, Factoid 6.5 terminal `1`)
as a `Mathlib.CategoryTheory` cartesian-closed category of information systems and
approximable maps — the formal counterpart of Scott’s remark.

**Status:** Not Yet (stretch) — blocked on Theorem 7.2; intentionally uses
`CategoryTheory` when attempted.
-/

namespace Scott1982

namespace InfoSys

-- TODO (stretch): `Category` / `CartesianClosed` instance via mathlib,
-- built from Prop 6.2 + Thm 7.2 + Factoid 6.5.

end InfoSys

end Scott1982
