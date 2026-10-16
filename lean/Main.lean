/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Statement
public import Proofs.Extensions

/-!
# Public results and axiom audit

The statement boundary uses only CSLib and Mathlib. The proofs construct actual
Boolean circuits using CSLib synthesis and the user's circuit library. These
guards fail if the theorem dependencies acquire an additional axiom.
-/

namespace IteratedFunctions

/-- info: 'IteratedFunctions.fixedPowerBound' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fixedPowerBound

/-- info: 'IteratedFunctions.fixedPowerOnBound' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fixedPowerOnBound

/-- info: 'IteratedFunctions.fixed_power_encoded' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fixed_power_encoded

/-- info: 'IteratedFunctions.image_sensitive' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms image_sensitive

end IteratedFunctions
