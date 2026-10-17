/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Statement
public import Proofs.Extensions
public import Proofs.Applications
public import Proofs.UniversalMap
public import Proofs.VariableTime
public import Proofs.Targets
public import Proofs.OrbitStructure
public import Proofs.BatchVariableTime
public import Proofs.LowerBound
public import Proofs.PrimeCycles
public import Proofs.NavigationCircuits
public import Proofs.SparseDisplacement
public import Proofs.StreamingRemainder
public import Proofs.EventualQueries
public import Proofs.LongTime
public import Proofs.TargetTimes
public import Proofs.VisitScheduleCircuits
public import Proofs.TypicalPowers
public import Proofs.ExponentLength
public import Proofs.ActivePowers
public import Proofs.AffineController
public import Proofs.SparseCounterTime
public import Proofs.SparseNavigation
public import Proofs.Spectrum

public import Proofs.NumberOfPowers

public import Proofs.InPlace

public import Proofs.ForestDuality

public import Proofs.CounterBatch

public import Proofs.SequentialSquaring

public import Proofs.PhaseIdentities

/-!
# Public results and axiom audit

The statement boundary uses only CSLib and Mathlib. The proofs construct actual
Boolean circuits using CSLib synthesis and the user's circuit library. These
guards fail if the theorem dependencies acquire an additional axiom.
-/

namespace IteratedFunctions

/-- info: 'IteratedFunctions.forestMarks_card' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms forestMarks_card

/-- info: 'IteratedFunctions.exists_forest_intervals' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_forest_intervals

/-- info: 'IteratedFunctions.forest_reachability_circuit' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms forest_reachability_circuit

/-- info: 'IteratedFunctions.sparse_counter_hitting_time' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sparse_counter_hitting_time

/-- info: 'IteratedFunctions.sparse_counter_visit_schedule' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sparse_counter_visit_schedule

/-- info: 'IteratedFunctions.sparse_coordinate_visit_schedule' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sparse_coordinate_visit_schedule

/-- info: 'IteratedFunctions.sparse_counter_variable_time' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sparse_counter_variable_time

/-- info: 'IteratedFunctions.sparse_counter_labels' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sparse_counter_labels

/-- info: 'IteratedFunctions.sparse_coordinate_variable_time' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sparse_coordinate_variable_time

/-- info: 'IteratedFunctions.controlled_family_power' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms controlled_family_power

/-- info: 'IteratedFunctions.controlled_family_variable_time' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms controlled_family_variable_time

/-- info: 'IteratedFunctions.affine_controller_power' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms affine_controller_power

/-- info: 'IteratedFunctions.affine_controller_polynomial' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms affine_controller_polynomial

/-- info: 'IteratedFunctions.affine_controller_variable_time' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms affine_controller_variable_time

/-- info: 'IteratedFunctions.active_mass_fixed_power' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms active_mass_fixed_power

/-- info: 'IteratedFunctions.almost_every_counter_power' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms almost_every_counter_power

/-- info: 'IteratedFunctions.ModulusCounter.remainder_of_power' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ModulusCounter.remainder_of_power

/-- info: 'IteratedFunctions.ModulusCounter.power_of_remainder' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ModulusCounter.power_of_remainder

/-- info: 'IteratedFunctions.ModulusCounter.hard_power_exponent_capacity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ModulusCounter.hard_power_exponent_capacity

/-- info: 'IteratedFunctions.ModulusCounter.batched_counter_power' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ModulusCounter.batched_counter_power

/-- info: 'IteratedFunctions.ModulusCounter.batch_lower_bounds' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ModulusCounter.batch_lower_bounds

/-- info: 'IteratedFunctions.ModulusCounter.batched_hard_counter_power' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ModulusCounter.batched_hard_counter_power

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

/-- info: 'IteratedFunctions.PrimeCycles.power_apply_mod' depends on axioms:
[propext, Quot.sound] -/
#guard_msgs in
#print axioms PrimeCycles.power_apply_mod

/-- info: 'IteratedFunctions.PrimeCycles.iterate_eq_iterate_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PrimeCycles.iterate_eq_iterate_iff

/-- info: 'IteratedFunctions.PrimeCycles.card_range_iterate' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PrimeCycles.card_range_iterate

/-- info: 'IteratedFunctions.PrimeCycles.classPrime_coprime' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PrimeCycles.classPrime_coprime

/-- info: 'IteratedFunctions.PrimeCycles.near_landau_lower_bound' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PrimeCycles.near_landau_lower_bound

/-- info: 'IteratedFunctions.sparse_counter_centralizer' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sparse_counter_centralizer

/-- info: 'IteratedFunctions.sparse_counter_power' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sparse_counter_power

/-- info: 'IteratedFunctions.sparse_coordinate_power' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sparse_coordinate_power

/-- info: 'IteratedFunctions.bounded_modulus_remainder' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bounded_modulus_remainder

/-- info: 'IteratedFunctions.synchronous_coalescence_optimized' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms synchronous_coalescence_optimized

/-- info: 'IteratedFunctions.recurring_target_optimized' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms recurring_target_optimized

/-- info: 'IteratedFunctions.eventually_always_target_optimized' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eventually_always_target_optimized

/-- info: 'IteratedFunctions.iterate_eq_projection_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms iterate_eq_projection_iff

/-- info: 'IteratedFunctions.iterate_normalizedTime' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms iterate_normalizedTime

/-- info: 'IteratedFunctions.variable_time_additive_optimized' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms variable_time_additive_optimized

/-- info: 'IteratedFunctions.checkpoint_depth_optimized' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms checkpoint_depth_optimized

/-- info: 'IteratedFunctions.first_target_time_optimized' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms first_target_time_optimized

/-- info: 'IteratedFunctions.halting_time' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms halting_time

/-- info: 'IteratedFunctions.visit_schedule_optimized' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms visit_schedule_optimized

/-- info: 'IteratedFunctions.visit_schedule_of_first' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms visit_schedule_of_first

/-- info: 'IteratedFunctions.visit_count_of_first' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms visit_count_of_first

/-- info: 'IteratedFunctions.iterate_eq_card_add_mod' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms iterate_eq_card_add_mod

/-- info: 'IteratedFunctions.card_add_mod_lt' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms card_add_mod_lt

/-- info: 'IteratedFunctions.cycle_test_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cycle_test_iff

/-- info: 'IteratedFunctions.cycleSpectrum_test' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cycleSpectrum_test

/-- info: 'IteratedFunctions.injective_spectrum_test' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms injective_spectrum_test

/-- info: 'IteratedFunctions.perm_symm_eq_iterate' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms perm_symm_eq_iterate

/-- info: 'IteratedFunctions.iterate_eq_iterate_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms iterate_eq_iterate_iff

/-- info: 'IteratedFunctions.card_range_iterate' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms card_range_iterate

/-- info: 'IteratedFunctions.exists_hard_power_of_budget_lt' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_hard_power_of_budget_lt

/-- info: 'IteratedFunctions.exists_hard_power' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_hard_power

/-- info: 'IteratedFunctions.InPlace.card_config' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InPlace.card_config

/-- info: 'IteratedFunctions.InPlace.reach_card_le_configs' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InPlace.reach_card_le_configs

/-- info: 'IteratedFunctions.InPlace.reach_card_le_time' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InPlace.reach_card_le_time

/-- info: 'IteratedFunctions.InPlace.reach_card_le_round' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InPlace.reach_card_le_round

/-- info: 'IteratedFunctions.InPlace.iterate_card_halting' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InPlace.iterate_card_halting

/-- info: 'IteratedFunctions.InPlace.inplace_fixed_power' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InPlace.inplace_fixed_power

/-- info: 'IteratedFunctions.InPlace.inplace_fixed_power_optimized' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InPlace.inplace_fixed_power_optimized

/-- info: 'IteratedFunctions.InPlace.inplace_configs_optimized' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InPlace.inplace_configs_optimized

/-- info: 'IteratedFunctions.InPlace.inplace_time_optimized' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InPlace.inplace_time_optimized

/-- info: 'IteratedFunctions.InPlace.inplace_halting' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InPlace.inplace_halting

/-- info: 'IteratedFunctions.InPlace.round_lower_bound' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InPlace.round_lower_bound

/-- info: 'IteratedFunctions.InPlace.round_bounds' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InPlace.round_bounds

/-- info: 'IteratedFunctions.ForestDuality.forest_duality' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ForestDuality.forest_duality

/-- info: 'IteratedFunctions.iterate_simulation' depends on axioms:
[propext, Quot.sound] -/
#guard_msgs in
#print axioms iterate_simulation

/-- info: 'IteratedFunctions.simulation_circuit' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms simulation_circuit

/-- info: 'IteratedFunctions.prodMap_power_circuit' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms prodMap_power_circuit

/-- info: 'IteratedFunctions.prodMap_power_circuit_left' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms prodMap_power_circuit_left

/-- info: 'IteratedFunctions.smul_zpow_circuit' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms smul_zpow_circuit

/-- info: 'IteratedFunctions.smul_iterate_circuit' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms smul_iterate_circuit

/-- info: 'IteratedFunctions.smul_inverse_circuit' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms smul_inverse_circuit

/-- info: 'IteratedFunctions.pairAction_iterate' depends on axioms:
[propext, Quot.sound] -/
#guard_msgs in
#print axioms pairAction_iterate

/-- info: 'IteratedFunctions.Universal.step_round' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Universal.step_round

/-- info: 'IteratedFunctions.Universal.step_iterate' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Universal.step_iterate

/-- info: 'IteratedFunctions.Universal.universal_power_circuit' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Universal.universal_power_circuit

/-- info: 'IteratedFunctions.SequentialSquaring.pow_carmichael_succ' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SequentialSquaring.pow_carmichael_succ

/-- info: 'IteratedFunctions.SequentialSquaring.pow_eq_pow_of_modEq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SequentialSquaring.pow_eq_pow_of_modEq

/-- info: 'IteratedFunctions.SequentialSquaring.iterate_square_reduced' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SequentialSquaring.iterate_square_reduced

/-- info: 'IteratedFunctions.SequentialSquaring.reducedExponent_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SequentialSquaring.reducedExponent_le

/-- info: 'IteratedFunctions.SequentialSquaring.crypto_table_entries' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SequentialSquaring.crypto_table_entries

/-- info: 'IteratedFunctions.canonicalTime_apply' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms canonicalTime_apply

/-- info: 'IteratedFunctions.iterate_eq_canonical_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms iterate_eq_canonical_iff

end IteratedFunctions
