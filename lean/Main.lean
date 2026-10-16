/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Statement
public import Proofs.Extensions
public import Proofs.Applications
public import Proofs.VariableTime
public import Proofs.Targets
public import Proofs.OrbitStructure
public import Proofs.BatchVariableTime
public import Proofs.LowerBound
public import Proofs.NavigationCircuits

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

/-- info: 'IteratedFunctions.fixed_power_optimized' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fixed_power_optimized

/-- info: 'IteratedFunctions.fixed_power_polynomial' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fixed_power_polynomial

/-- info: 'IteratedFunctions.permutation_inverse_encoded' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms permutation_inverse_encoded

/-- info: 'IteratedFunctions.variable_time_optimized' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms variable_time_optimized

/-- info: 'IteratedFunctions.first_target_state' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms first_target_state

/-- info: 'IteratedFunctions.halting_computation' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms halting_computation

/-- info: 'IteratedFunctions.target_reachability' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms target_reachability

/-- info: 'IteratedFunctions.batched_fixed_power_optimized' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms batched_fixed_power_optimized

/-- info: 'IteratedFunctions.batched_variable_time_optimized' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms batched_variable_time_optimized

/-- info: 'IteratedFunctions.cycle_labels_optimized' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cycle_labels_optimized

/-- info: 'IteratedFunctions.depth_circuit_optimized' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms depth_circuit_optimized

/-- info: 'IteratedFunctions.reachability_hitting_time' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms reachability_hitting_time

/-- info: 'IteratedFunctions.hittingTime_spec' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hittingTime_spec

/-- info: 'IteratedFunctions.matching_lower_bound' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms matching_lower_bound

end IteratedFunctions
