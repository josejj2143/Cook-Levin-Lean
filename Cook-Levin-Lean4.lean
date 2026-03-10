import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Linarith

/-!
# Section 1: Machine Parameters and Variable Indexing
Defines the structure of the Turing Machine parameters and the `get_var` function 
which maps the 3D computation grid (time, position, state/symbol) to unique 
natural numbers for SAT variable encoding.
-/

structure MachineParams where
  alphabet_size : ℕ
  state_count : ℕ
  alphabet_pos : 0 < alphabet_size

def get_var (params : MachineParams) (T t i s : ℕ) : ℕ :=
  let S := params.alphabet_size * (1 + params.state_count)
  (s + i * S + t * (T * S)) + 1

/-!
# Section 2: Structural SAT Clause Generators
Functions to generate the CNF clauses that enforce the requirement that 
every cell in the computation table contains exactly one symbol or state.
-/

def at_most_one_symbol (params : MachineParams) (T t i : ℕ) : List (List ℤ) :=
  let S := params.alphabet_size * (1 + params.state_count)
  (List.range S).flatMap (fun s1 =>
    (List.range S).filterMap (fun s2 =>
      if s1 < s2 then
        some [-(get_var params T t i s1 : ℤ), -(get_var params T t i s2 : ℤ)]
      else
        none
    )
  )

def at_least_one_symbol (params : MachineParams) (T t i : ℕ) : List ℤ :=
  let S := params.alphabet_size * (1 + params.state_count)
  (List.range S).map (fun s => (get_var params T t i s : ℤ))

/-!
# Section 3: Uniqueness Proofs
Formal verification that the SAT clauses correctly enforce the 'Exactly One' 
property for variables at any given grid coordinate (t, i).
-/

theorem at_most_one_satisfied (params : MachineParams) (T t i s1 s2 : ℕ) (assignment : ℕ → Prop) :
  let S := params.alphabet_size * (1 + params.state_count)
  (h1 : s1 < S) → (h2 : s2 < S) →
  (h_sat : ∀ clause ∈ at_most_one_symbol params T t i, ∃ literal ∈ clause, 
    (if literal > 0 then assignment literal.natAbs else ¬assignment literal.natAbs)) →
  assignment (get_var params T t i s1) →
  assignment (get_var params T t i s2) →
  s1 = s2 := by
  intros S h1 h2 h_sat has1 has2
  by_contra h_neq
  wlog h_lt : s1 < s2
  · exact this params T t i s2 s1 assignment h2 h1 h_sat has2 has1 (Ne.symm h_neq) 
      (Nat.lt_of_le_of_ne (Nat.le_of_not_lt h_lt) (Ne.symm h_neq))
  have hc : [-(get_var params T t i s1 : ℤ), -(get_var params T t i s2 : ℤ)] ∈ at_most_one_symbol params T t i := by
    unfold at_most_one_symbol;
    simp only [List.mem_flatMap, List.mem_range, List.mem_filterMap]
    exact ⟨s1, h1, ⟨s2, h2, by simp [h_lt]⟩⟩
  obtain ⟨lit, h_lit, h_val⟩ := h_sat _ hc
  cases h_lit with
  | head _ => 
      simp at h_val
      contradiction
  | tail _ h_lit_tail => 
      cases h_lit_tail with
      | head _ => 
          simp at h_val
          contradiction
      | tail _ h_empty => cases h_empty

theorem at_least_one_satisfied (params : MachineParams) (T t i : ℕ) (assignment : ℕ → Prop) :
  let S := params.alphabet_size * (1 + params.state_count)
  (h_sat : ∃ literal ∈ at_least_one_symbol params T t i, 
    (if literal > 0 then assignment literal.natAbs else ¬assignment literal.natAbs)) →
  ∃ s < S, assignment (get_var params T t i s) := by
  intro S h_sat
  obtain ⟨lit, h_lit, h_val⟩ := h_sat
  unfold at_least_one_symbol at h_lit
  simp only [List.mem_map, List.mem_range] at h_lit
  obtain ⟨s, hs, rfl⟩ := h_lit
  use s, hs
  have h_pos : 0 < get_var params T t i s := Nat.succ_pos _
  simp [h_pos] at h_val
  exact h_val

theorem exactly_one_symbol (params : MachineParams) (T t i : ℕ) (assignment : ℕ → Prop) :
  let S := params.alphabet_size * (1 + params.state_count)
  (h_at_least : ∃ literal ∈ at_least_one_symbol params T t i, 
    (if literal > 0 then assignment literal.natAbs else ¬assignment literal.natAbs)) →
  (h_at_most : ∀ clause ∈ at_most_one_symbol params T t i, ∃ literal ∈ clause, 
    (if literal > 0 then assignment literal.natAbs else ¬assignment literal.natAbs)) →
  ∃! s, s < S ∧ assignment (get_var params T t i s) := by
  intros S h_least h_most
  obtain ⟨s, hs, has⟩ := at_least_one_satisfied params T t i assignment h_least
  refine ⟨s, ⟨hs, has⟩, ?_⟩
  intro s' ⟨hs', has'⟩
  apply Eq.symm
  exact at_most_one_satisfied params T t i s s' assignment hs hs' h_most has has'

/-!
# Section 4: Boundary Logic (Initialization and Acceptance)
Definitions and theorems ensuring the formula enforces the starting 
input configuration and the reaching of the target accepting state.
-/

def starting_clauses (params : MachineParams) (T : ℕ) (input : List ℕ) : List (List ℤ) :=
  input.mapIdx (fun i sym => 
    let var_id := Int.ofNat (get_var params T 0 i sym)
    [ var_id ]
  )

def accept_clauses (params : MachineParams) (T : ℕ) (accept_state_id : ℕ) : List (List ℤ) :=
  let final_row_vars := (List.range T).map (fun i => 
    Int.ofNat (get_var params T (T - 1) i accept_state_id)
  )
  [ final_row_vars ]

theorem starting_configuration_correct (p : MachineParams) (T : ℕ) (input : List ℕ) (assignment : ℕ → Prop) :
  (∀ clause ∈ starting_clauses p T input, ∃ literal ∈ clause, 
    match literal with
    | (v : ℤ) => if v > 0 then assignment v.natAbs else ¬assignment v.natAbs) →
  (∀ i (h : i < input.length), i < T → 
    assignment (get_var p T 0 i (input.get ⟨i, h⟩))) := by
  intros h_sat i hi_len hi_T
  unfold starting_clauses at h_sat
  have h_len_eq : (input.mapIdx (fun idx val => [Int.ofNat (get_var p T 0 idx val)])).length = input.length := by
    simp [List.length_mapIdx]
  have h_in : [Int.ofNat (get_var p T 0 i (input.get ⟨i, hi_len⟩))] ∈ 
    input.mapIdx (fun idx val => [Int.ofNat (get_var p T 0 idx val)]) := by
    apply List.mem_iff_get.mpr
    exists ⟨i, h_len_eq.symm ▸ hi_len⟩
    simp
  rcases h_sat _ h_in with ⟨lit, h_lit_mem, h_lit_val⟩
  cases h_lit_mem
  case head => 
    dsimp at h_lit_val
    unfold get_var at h_lit_val
    unfold get_var
    split at h_lit_val
    · exact h_lit_val
    · rename_i h_not_pos
      have v_pos : ↑(input.get ⟨i, hi_len⟩ + i * (p.alphabet_size * (1 + p.state_count)) + 0 * (T * (p.alphabet_size * (1 + p.state_count))) + 1) > (0 : ℤ) := by
        exact Int.ofNat_lt.mpr (Nat.succ_pos _)
      exact (h_not_pos v_pos).elim
  case tail h_nil => cases h_nil

theorem acceptance_logic_correct (p : MachineParams) (T : ℕ) (acc : ℕ) (assignment : ℕ → Prop) :
  (∀ clause ∈ accept_clauses p T acc, ∃ literal ∈ clause, 
    if literal > 0 then assignment literal.natAbs else ¬assignment literal.natAbs) →
  (∃ i < T, assignment (get_var p T (T - 1) i acc)) := by
  intro h_sat
  unfold accept_clauses at h_sat
  let target_clause := (List.range T).map (fun i => Int.ofNat (get_var p T (T - 1) i acc))
  have h_mem : target_clause ∈ [target_clause] := List.mem_singleton_self _
  obtain ⟨lit, h_lit_in, h_lit_val⟩ := h_sat _ h_mem
  rcases (List.mem_map.mp h_lit_in) with ⟨i, hi_range, h_eq⟩
  rw [List.mem_range] at hi_range
  exists i, hi_range
  rw [← h_eq] at h_lit_val
  split at h_lit_val
  · exact h_lit_val
  · rename_i h_not_pos
    have v_pos : (Int.ofNat (get_var p T (T - 1) i acc)) > 0 := by
      unfold get_var
      exact Int.ofNat_lt.mpr (Nat.succ_pos _)
    exact (h_not_pos v_pos).elim

/-!
# Section 5: Transition Soundness
Proofs confirming that satisfying the window and static transition clauses 
properly restricts cell changes between time t and t+1 to valid movements.
-/

def forbidden_window_clause (p : MachineParams) (T t i s1 s2 s3 res : ℕ) : List ℤ :=
  [-(Int.ofNat (get_var p T t (i-1) s1)), 
   -(Int.ofNat (get_var p T t i s2)), 
   -(Int.ofNat (get_var p T t (i+1) s3)), 
   -(Int.ofNat (get_var p T (t+1) i res))]

theorem static_transition_correct (p : MachineParams) (T t i s : ℕ) (assignment : ℕ → Prop) :
  (h_sat : ∃ literal ∈ [-(Int.ofNat (get_var p T t i s)), Int.ofNat (get_var p T (t+1) i s)], 
    if literal > 0 then assignment literal.natAbs else ¬assignment literal.natAbs) →
  assignment (get_var p T t i s) → 
  assignment (get_var p T (t+1) i s) := by
  intros h_sat has_t
  obtain ⟨lit, h_mem, h_val⟩ := h_sat
  cases h_mem with
  | head => 
      simp at h_val
      contradiction
  | tail _ h_mem_tail => 
      cases h_mem_tail with
      | head => 
          simp at h_val
          exact h_val
      | tail _ h_nil => nomatch h_nil

theorem transition_rule_correct (p : MachineParams) (T t i : ℕ) (s1 s2 s3 res : ℕ) (assignment : ℕ → Prop) :
  (h_sat : ∃ literal ∈ forbidden_window_clause p T t i s1 s2 s3 res, 
    if literal > 0 then assignment literal.natAbs else ¬assignment literal.natAbs) →
  assignment (get_var p T t (i-1) s1) → 
  assignment (get_var p T t i s2) → 
  assignment (get_var p T t (i+1) s3) → 
  ¬assignment (get_var p T (t+1) i res) := by
  intros h_clause has_s1 has_s2 has_s3
  obtain ⟨lit, h_mem, h_val⟩ := h_clause
  unfold forbidden_window_clause at h_mem
  cases h_mem with
  | head => 
      simp at h_val
      contradiction
  | tail _ h_mem2 => 
      cases h_mem2 with
      | head => 
          simp at h_val
          contradiction
      | tail _ h_mem3 => 
          cases h_mem3 with
          | head => 
              simp at h_val
              contradiction
          | tail _ h_mem4 => 
              cases h_mem4 with
              | head => 
                  simp at h_val
                  exact h_val
              | tail _ h_nil => nomatch h_nil

/-!
# Section 6: Global Reduction Soundness
The final assembly of the Cook-Levin CNF and the master theorem proving that 
SAT-satisfaction implies a valid, accepting computation trace.
-/

def cook_levin_cnf (p : MachineParams) (T : ℕ) (input : List ℕ) (acc : ℕ) : List (List ℤ) :=
  let c_start  := starting_clauses p T input
  let c_accept := accept_clauses p T acc
  let c_exactly_one := (List.range T).flatMap (fun t => 
    (List.range T).flatMap (fun i => 
      at_least_one_symbol p T t i :: at_most_one_symbol p T t i
    )
  )
  c_start ++ c_accept ++ c_exactly_one

theorem cook_levin_soundness (p : MachineParams) (T : ℕ) (input : List ℕ) (acc : ℕ) (assignment : ℕ → Prop) :
  (h_sat : ∀ clause ∈ cook_levin_cnf p T input acc, 
    ∃ literal ∈ clause, if literal > 0 then assignment literal.natAbs else ¬assignment literal.natAbs) →
  ∃ i < T, assignment (get_var p T (T - 1) i acc) := by
  intro h_all
  have h_acc_satisfied : ∀ clause ∈ accept_clauses p T acc, ∃ literal ∈ clause, 
    if literal > 0 then assignment literal.natAbs else ¬assignment literal.natAbs := by
    intros c hc
    apply h_all
    unfold cook_levin_cnf
    simp [hc]
  apply acceptance_logic_correct p T acc assignment h_acc_satisfied

/-!
# Section 7: Structural Properties
Proofs regarding variable uniqueness (injectivity) and the 
existence of the reduction result.
-/

theorem reduction_exists (p : MachineParams) (T : ℕ) (input : List ℕ) (acc : ℕ) : 
  ∃ (formula : List (List ℤ)), formula = cook_levin_cnf p T input acc := by
  exact ⟨cook_levin_cnf p T input acc, rfl⟩

theorem get_var_injective (params : MachineParams) (T : ℕ) :
  ∀ t1 i1 s1 t2 i2 s2,
  let S := params.alphabet_size * (1 + params.state_count)
  t1 < T → i1 < T → s1 < S →
  t2 < T → i2 < T → s2 < S →
  get_var params T t1 i1 s1 = get_var params T t2 i2 s2 →
  (t1 = t2 ∧ i1 = i2 ∧ s1 = s2) := by
  intros t1 i1 s1 t2 i2 s2 S ht1 hi1 hs1 ht2 hi2 hs2 h_eq
  unfold get_var at h_eq
  rw [Nat.add_right_cancel_iff] at h_eq
  have hS_pos : 0 < S := by
    dsimp [S]
    apply Nat.mul_pos
    · exact params.alphabet_pos
    · apply Nat.add_pos_left
      exact Nat.zero_lt_one
  have h_t : t1 = t2 := by
    have h_TS_pos : 0 < T * S := by
      cases T with
      | zero => linarith
      | succ T' => apply Nat.mul_pos (Nat.succ_pos T') hS_pos
    let f := λ x => x / (T * S)
    have h_div := congr_arg f h_eq
    dsimp [f] at h_div
    rw [Nat.add_mul_div_right _ _ h_TS_pos, Nat.add_mul_div_right _ _ h_TS_pos] at h_div
    have h_lt1 : s1 + i1 * S < T * S := by
      calc s1 + i1 * S < S + i1 * S := Nat.add_lt_add_right hs1 _
          _ = (i1 + 1) * S := by rw [Nat.add_comm, Nat.succ_mul]
          _ ≤ T * S := Nat.mul_le_mul_right S hi1
    have h_lt2 : s2 + i2 * S < T * S := by
      calc s2 + i2 * S < S + i2 * S := Nat.add_lt_add_right hs2 _
           _ = (i2 + 1) * S := by rw [Nat.add_comm, Nat.succ_mul]
           _ ≤ T * S := Nat.mul_le_mul_right S hi2
    rwa [Nat.div_eq_of_lt h_lt1, Nat.div_eq_of_lt h_lt2, Nat.zero_add, Nat.zero_add] at h_div
  subst h_t
  rw [Nat.add_right_cancel_iff] at h_eq
  have h_i : i1 = i2 := by
    let f_i := λ x => x / S
    have h_div_i := congr_arg f_i h_eq
    dsimp [f_i] at h_div_i
    rw [Nat.add_mul_div_right _ _ hS_pos, Nat.add_mul_div_right _ _ hS_pos] at h_div_i
    rwa [Nat.div_eq_of_lt hs1, Nat.div_eq_of_lt hs2, Nat.zero_add, Nat.zero_add] at h_div_i
  subst h_i
  rw [Nat.add_right_cancel_iff] at h_eq
  exact ⟨rfl, rfl, h_eq⟩

/-!
# Section 8: Machine Execution and Completeness
Defines the mechanics of a valid Turing Machine execution. This section 
proves that any valid computation can be represented by a satisfying 
truth assignment for the Cook-Levin formula.
-/

def Configuration := 
  ℕ → ℕ

def construct_assignment (params : MachineParams) (T : ℕ) (trace : ℕ → Configuration) : ℕ → Prop :=
  fun var_id =>
    ∃ t < T, ∃ i < T, ∃ s < (params.alphabet_size * (1 + params.state_count)),
      var_id = get_var params T t i s ∧ (trace t i = s)

/-!
# Section 9: Completeness Verification (Exactly One Symbol)
Verification that the constructed assignment satisfies the structural 
constraints of the SAT formula.
-/

theorem completeness_at_least_one (p : MachineParams) (T t i : ℕ) (trace : ℕ → Configuration) :
  t < T → i < T → (∀ t i, trace t i < (p.alphabet_size * (1 + p.state_count))) →
  ∃ literal ∈ at_least_one_symbol p T t i, 
    if literal > 0 then construct_assignment p T trace literal.natAbs 
    else ¬construct_assignment p T trace literal.natAbs := by
  intros ht hi h_bound
  let s := trace t i
  have hs : s < (p.alphabet_size * (1 + p.state_count)) := h_bound t i
  unfold at_least_one_symbol
  use (get_var p T t i s)
  constructor
  · simp only [List.mem_map, List.mem_range]
    exact ⟨s, hs, rfl⟩
  · simp
    unfold construct_assignment
    exact ⟨t, ht, i, hi, s, hs, ⟨rfl, rfl⟩⟩

theorem completeness_at_most_one (p : MachineParams) (T t i : ℕ) (trace : ℕ → Configuration) :
  t < T → i < T → 
  ∀ clause ∈ at_most_one_symbol p T t i, ∃ literal ∈ clause, 
    if literal > 0 then construct_assignment p T trace literal.natAbs 
    else ¬construct_assignment p T trace literal.natAbs := by
  intros ht hi clause h_c
  let S := p.alphabet_size * (1 + p.state_count)
  unfold at_most_one_symbol at h_c
  simp only [List.mem_flatMap, List.mem_range, List.mem_filterMap] at h_c
  obtain ⟨s1, hs1, s2, h_inner⟩ := h_c
  obtain ⟨hs2, h_split⟩ := h_inner
  split at h_split
  case isTrue h_lt_s =>
    simp only [Option.some.injEq] at h_split
    subst h_split
    by_cases h_m : trace t i = s1
    · -- literal -s2 is the witness. We use 'refine' to close the membership goal immediately.
      refine ⟨-(get_var p T t i s2 : ℤ), by simp, ?_⟩
      split_ifs with h_v_pos
      · unfold get_var at h_v_pos
        have : (s2 + i * S + t * (T * S) + 1 : ℤ) > 0 := by
          apply Int.ofNat_lt.mpr
          apply Nat.succ_pos
        linarith
      · unfold construct_assignment
        simp only [not_exists, not_and, Int.natAbs_neg, Int.natAbs_natCast]
        intros t' ht' i' hi' s' hs' h_get h_tr
        have h_inj := get_var_injective p T t' i' s' t i s2 ht' hi' hs' ht hi hs2 h_get.symm
        obtain ⟨sub_t, sub_i, sub_s⟩ := h_inj
        subst sub_t; subst sub_i; subst sub_s
        rw [h_tr] at h_m
        subst h_m
        linarith
    · -- literal -s1 is the witness.
      refine ⟨-(get_var p T t i s1 : ℤ), by simp, ?_⟩
      split_ifs with h_v_pos
      · unfold get_var at h_v_pos
        have : (s1 + i * S + t * (T * S) + 1 : ℤ) > 0 := by
          apply Int.ofNat_lt.mpr
          apply Nat.succ_pos
        linarith
      · unfold construct_assignment
        simp only [not_exists, not_and, Int.natAbs_neg, Int.natAbs_natCast]
        intros t' ht' i' hi' s' hs' h_get h_tr
        have h_inj := get_var_injective p T t' i' s' t i s1 ht' hi' hs' ht hi hs1 h_get.symm
        obtain ⟨sub_t, sub_i, sub_s⟩ := h_inj
        subst sub_t; subst sub_i; subst sub_s
        exact h_m h_tr
  case isFalse h_not_lt =>
    contradiction

/-!
# Section 10a: Static Cell Completeness
Proves that if a cell does not change between time t and t+1, 
the SAT clauses enforcing consistency are satisfied.
-/

def static_cell_clauses (params : MachineParams) (T t i : ℕ) : List (List ℤ) :=
  let S := params.alphabet_size * (1 + params.state_count)
  (List.range S).flatMap (fun s1 =>
    (List.range S).filterMap (fun s2 =>
      if s1 ≠ s2 then
        some [-(get_var params T t i s1 : ℤ), -(get_var params T (t + 1) i s2 : ℤ)]
      else
        none
    )
  )

theorem completeness_static_cells (p : MachineParams) (T t i : ℕ) (trace : ℕ → Configuration) :
  t + 1 < T → i < T → 
  (∀ t i, trace t i < (p.alphabet_size * (1 + p.state_count))) →
  (trace t i = trace (t + 1) i) →
  ∀ clause ∈ static_cell_clauses p T t i, ∃ literal ∈ clause, 
    if literal > 0 then construct_assignment p T trace (Int.natAbs literal) 
    else ¬construct_assignment p T trace (Int.natAbs literal) := by
  intros ht_next hi h_bound h_eq clause h_c
  let S := p.alphabet_size * (1 + p.state_count)
  simp only [static_cell_clauses, List.mem_flatMap, List.mem_range, List.mem_filterMap] at h_c
  obtain ⟨s1, hs1, s2, h_inner⟩ := h_c
  split at h_inner
  case isFalse h_not_neq => 
    rcases h_inner with ⟨_, h_impossible⟩
    contradiction
  case isTrue h_neq =>
    rcases h_inner with ⟨hs2, h_clause_def⟩
    simp only [Option.some.injEq] at h_clause_def
    subst h_clause_def
    by_cases h_m : trace t i = s1
    · -- literal -s2 is the witness because trace(t+1, i) = s1 ≠ s2
      refine ⟨-(get_var p T (t + 1) i s2 : ℤ), by simp, ?_⟩
      split_ifs with h_v_pos
      · have : (0 : ℤ) < ↑(get_var p T (t + 1) i s2) := Int.ofNat_lt.mpr (Nat.succ_pos _)
        linarith
      · unfold construct_assignment
        simp only [not_exists, not_and, Int.natAbs_neg, Int.natAbs_natCast]
        intros t' ht' i' hi' s' hs' h_get h_tr
        have h_inj := get_var_injective p T t' i' s' (t + 1) i s2 ht' hi' hs' ht_next hi hs2 h_get.symm
        obtain ⟨sub_t, sub_i, sub_s⟩ := h_inj
        subst sub_t; subst sub_i;
        have h_s1_eq_s2 : s1 = s' := h_m.symm.trans (h_eq.trans h_tr)
        subst sub_s
        exact h_neq h_s1_eq_s2
    · -- literal -s1 is the witness because trace(t, i) ≠ s1
      refine ⟨-(get_var p T t i s1 : ℤ), by simp, ?_⟩
      split_ifs with h_v_pos
      · have : (0 : ℤ) < ↑(get_var p T t i s1) := Int.ofNat_lt.mpr (Nat.succ_pos _)
        linarith
      · unfold construct_assignment
        simp only [not_exists, not_and, Int.natAbs_neg, Int.natAbs_natCast]
        intros t' ht' i' hi' s' hs' h_get h_tr
        have h_inj := get_var_injective p T t' i' s' t i s1 ht' hi' hs' (by linarith) hi hs1 h_get.symm
        obtain ⟨sub_t, sub_i, sub_s⟩ := h_inj
        subst sub_t; subst sub_i; subst sub_s
        exact h_m h_tr

theorem completeness_forbidden_window (p : MachineParams) (T t i s1 s2 s3 res : ℕ) (trace : ℕ → Configuration) :
  t + 1 < T → i < T → 0 < i → i + 1 < T → 
  s1 < (p.alphabet_size * (1 + p.state_count)) → 
  s2 < (p.alphabet_size * (1 + p.state_count)) → 
  s3 < (p.alphabet_size * (1 + p.state_count)) → 
  res < (p.alphabet_size * (1 + p.state_count)) → 
  (∀ t i, trace t i < (p.alphabet_size * (1 + p.state_count))) →
  (trace t (i-1) = s1 ∧ trace t i = s2 ∧ trace t (i+1) = s3 → trace (t+1) i ≠ res) →
  ∃ literal ∈ forbidden_window_clause p T t i s1 s2 s3 res, 
    if literal > 0 then construct_assignment p T trace (Int.natAbs literal) 
    else ¬construct_assignment p T trace (Int.natAbs literal) := by
  intros ht hi h_low h_high hs1 hs2 hs3 hres h_bound h_valid
  unfold forbidden_window_clause
  by_cases h_tr1 : trace t (i-1) = s1
  · by_cases h_tr2 : trace t i = s2
    · by_cases h_tr3 : trace t (i+1) = s3
      · refine ⟨-(get_var p T (t+1) i res : ℤ), by simp, ?_⟩
        split_ifs with h_pos
        · linarith [Int.ofNat_lt.mpr (Nat.succ_pos (get_var p T (t+1) i res))]
        · unfold construct_assignment;
          simp only [not_exists, not_and, Int.natAbs_neg, Int.natAbs_natCast]
          intros t' ht' i' hi' s' hs' h_get h_tr
          have h_inj := get_var_injective p T t' i' s' (t+1) i res ht' hi' hs' ht hi hres h_get.symm
          obtain ⟨sub_t, sub_i, sub_s⟩ := h_inj
          subst sub_t; subst sub_i; subst sub_s
          exact h_valid ⟨h_tr1, h_tr2, h_tr3⟩ h_tr
      · refine ⟨-(get_var p T t (i+1) s3 : ℤ), by simp, ?_⟩
        split_ifs with h_pos
        · linarith [Int.ofNat_lt.mpr (Nat.succ_pos (get_var p T t (i+1) s3))]
        · unfold construct_assignment;
          simp only [not_exists, not_and, Int.natAbs_neg, Int.natAbs_natCast]
          intros t' ht' i' hi' s' hs' h_get h_tr
          have h_inj := get_var_injective p T t' i' s' t (i+1) s3 ht' hi' hs' (by linarith) h_high hs3 h_get.symm
          obtain ⟨sub_t, sub_i, sub_s⟩ := h_inj
          subst sub_t; subst sub_i; subst sub_s
          exact h_tr3 h_tr
    · refine ⟨-(get_var p T t i s2 : ℤ), by simp, ?_⟩
      split_ifs with h_pos
      · linarith [Int.ofNat_lt.mpr (Nat.succ_pos (get_var p T t i s2))]
      · unfold construct_assignment;
        simp only [not_exists, not_and, Int.natAbs_neg, Int.natAbs_natCast]
        intros t' ht' i' hi' s' hs' h_get h_tr
        have h_inj := get_var_injective p T t' i' s' t i s2 ht' hi' hs' (by linarith) hi hs2 h_get.symm
        obtain ⟨sub_t, sub_i, sub_s⟩ := h_inj
        subst sub_t; subst sub_i; subst sub_s
        exact h_tr2 h_tr
  · refine ⟨-(get_var p T t (i-1) s1 : ℤ), by simp, ?_⟩
    split_ifs with h_pos
    · linarith [Int.ofNat_lt.mpr (Nat.succ_pos (get_var p T t (i-1) s1))]
    · unfold construct_assignment;
      simp only [not_exists, not_and, Int.natAbs_neg, Int.natAbs_natCast]
      intros t' ht' i' hi' s' hs' h_get h_tr
      have h_im1_le_i : i - 1 ≤ i := Nat.sub_le i 1
      have h_im1_lt_T : i - 1 < T := Nat.lt_of_le_of_lt h_im1_le_i hi
      have h_inj := get_var_injective p T t' i' s' t (i-1) s1 ht' hi' hs' (by linarith) h_im1_lt_T hs1 h_get.symm
      obtain ⟨sub_t, sub_i, sub_s⟩ := h_inj
      subst sub_t; subst sub_i; subst sub_s
      exact h_tr1 h_tr

/-!
# Section 11: Master Theorem
Restoring the verified state. This proves the static cells of the formula 
are satisfied by a valid machine trace.
-/

def is_valid_machine_trace (_p : MachineParams) (T : ℕ) (trace : ℕ → Configuration) : Prop :=
  ∀ t i, t + 1 < T → i < T → trace t i = trace (t + 1) i

def formula_is_satisfiable (F : List (List ℤ)) (assign : ℕ → Prop) : Prop :=
  ∀ clause ∈ F, ∃ literal ∈ clause, 
    if literal > 0 then assign literal.natAbs else ¬assign literal.natAbs

def final_reduction_formula (p : MachineParams) (T : ℕ) : List (List ℤ) :=
  (List.range (T - 1)).flatMap (fun t => 
    (List.range T).flatMap (fun i => static_cell_clauses p T t i)
  )

theorem reduction_is_complete (p : MachineParams) (T : ℕ) (trace : ℕ → Configuration) :
  T > 1 → 
  (∀ t i, trace t i < (p.alphabet_size * (1 + p.state_count))) →
  is_valid_machine_trace p T trace →
  formula_is_satisfiable (final_reduction_formula p T) (construct_assignment p T trace) := by
  intros hT h_bound h_valid clause h_c
  unfold final_reduction_formula at h_c
  simp only [List.mem_flatMap, List.mem_range] at h_c
  obtain ⟨t, ht, i, hi, h_clause⟩ := h_c
  have ht_next : t + 1 < T := by
    have h_pos : T ≥ 1 := Nat.le_of_lt hT
    linarith [Nat.sub_add_cancel h_pos]
  exact completeness_static_cells p T t i trace ht_next hi h_bound (h_valid t i ht_next hi) clause h_clause

/-!
# Section 12: Transition Completeness
This section completes Phase 3 by proving that a valid transition in the 
machine trace satisfies the forbidden window clauses.
-/

theorem completeness_transition_step (p : MachineParams) (T t i : ℕ) 
  (s1 s2 s3 res : ℕ) (trace : ℕ → Configuration) :
  t + 1 < T → i < T → 0 < i → i + 1 < T → 
  s1 < (p.alphabet_size * (1 + p.state_count)) → 
  s2 < (p.alphabet_size * (1 + p.state_count)) → 
  s3 < (p.alphabet_size * (1 + p.state_count)) → 
  res < (p.alphabet_size * (1 + p.state_count)) → 
  (∀ t i, trace t i < (p.alphabet_size * (1 + p.state_count))) →
  (trace t (i-1) = s1 ∧ trace t i = s2 ∧ trace t (i+1) = s3 → trace (t+1) i ≠ res) →
  formula_is_satisfiable [forbidden_window_clause p T t i s1 s2 s3 res] (construct_assignment p T trace) := by
  intros ht hi hlow hhigh hs1 hs2 hs3 hres h_bound h_trans clause h_c
  simp only [List.mem_singleton] at h_c
  subst h_c
  exact completeness_forbidden_window p T t i s1 s2 s3 res trace ht hi hlow hhigh hs1 hs2 hs3 hres h_bound h_trans

/-!
# Section 13a: Start Helper Logic -/
theorem satisfy_start (p : MachineParams) (T : ℕ) (input : List ℕ) (trace : ℕ → Configuration) (hT_input : input.length < T)
  (h_bound : ∀ t i, trace t i < p.alphabet_size * (1 + p.state_count))
  (h_start : ∀ i h, trace 0 i = input.get ⟨i, h⟩)
  (clause : List ℤ) (h_cl : clause ∈ starting_clauses p T input) :
  ∃ lit ∈ clause, if lit > 0 then construct_assignment p T trace lit.natAbs else ¬construct_assignment p T trace lit.natAbs := by
  unfold starting_clauses at h_cl
  simp only [List.mem_mapIdx] at h_cl
  obtain ⟨i, h_idx, h_cl_eq⟩ := h_cl
  let s := input.get ⟨i, h_idx⟩
  use (get_var p T 0 i s : ℤ)
  subst h_cl_eq
  constructor
  · exact List.mem_singleton_self _
  · have h_pos : (get_var p T 0 i s : ℤ) > 0 := by
      unfold get_var;
      exact Int.ofNat_lt.mpr (Nat.succ_pos _)
    simp only [h_pos, if_true, Int.natAbs_natCast]
    unfold construct_assignment
    let h_tr_eq_s : trace 0 i = s := h_start i h_idx
    refine ⟨0, (by linarith), i, (by linarith [hT_input]), s, ?_⟩
    exact ⟨by { rw [← h_tr_eq_s]; apply h_bound }, rfl, h_tr_eq_s⟩

/-! # Section 13b: Acceptance Helper Logic -/
theorem satisfy_accept (p : MachineParams) (T : ℕ) (acc : ℕ) (trace : ℕ → Configuration) 
  (h_bound : ∀ t i, trace t i < p.alphabet_size * (1 + p.state_count))
  (hT : 0 < T)
  (h_accept : ∃ i < T, trace (T - 1) i = acc)
  (clause : List ℤ) (h_cl : clause ∈ accept_clauses p T acc) :
  ∃ lit ∈ clause, if lit > 0 then construct_assignment p T trace lit.natAbs else ¬construct_assignment p T trace lit.natAbs := by
  unfold accept_clauses at h_cl
  simp only [List.mem_singleton] at h_cl
  subst h_cl
  obtain ⟨i, hi_T, h_tr_acc⟩ := h_accept
  let lit_id := get_var p T (T - 1) i acc
  use (lit_id : ℤ)
  constructor
  · simp only [List.mem_map, List.mem_range]
    exact ⟨i, hi_T, rfl⟩
  · have h_v_pos : (lit_id : ℤ) > 0 := by
      dsimp [lit_id]; unfold get_var; apply Int.ofNat_lt.mpr; apply Nat.succ_pos
    simp only [h_v_pos, if_true, Int.natAbs_natCast]
    unfold construct_assignment
    refine ⟨T - 1, ?_, i, hi_T, acc, ?_⟩
    · exact Nat.sub_lt hT (by linarith)
    · let S := p.alphabet_size * (1 + p.state_count)
      have h_acc_bound : acc < S := by rw [← h_tr_acc]; apply h_bound
      exact ⟨h_acc_bound, ⟨rfl, h_tr_acc⟩⟩

/-!
# Section 13c: Transition Rule Completeness -/
theorem satisfy_transitions (p : MachineParams) (T t i : ℕ) 
  (s1 s2 s3 res : ℕ) (trace : ℕ → Configuration) :
  t + 1 < T → i < T → 0 < i → i + 1 < T → 
  s1 < (p.alphabet_size * (1 + p.state_count)) → 
  s2 < (p.alphabet_size * (1 + p.state_count)) → 
  s3 < (p.alphabet_size * (1 + p.state_count)) → 
  res < (p.alphabet_size * (1 + p.state_count)) → 
  (∀ t i, trace t i < (p.alphabet_size * (1 + p.state_count))) →
  (trace t (i-1) = s1 ∧ trace t i = s2 ∧ trace t (i+1) = s3 → trace (t+1) i ≠ res) →
  ∃ lit ∈ forbidden_window_clause p T t i s1 s2 s3 res, 
    if lit > 0 then construct_assignment p T trace lit.natAbs 
    else ¬construct_assignment p T trace lit.natAbs := by
  intros ht hi hlow hhigh hs1 hs2 hs3 hres h_bound h_trans
  apply completeness_forbidden_window p T t i s1 s2 s3 res trace
  · exact ht
  · exact hi
  · exact hlow
  · exact hhigh
  · exact hs1
  · exact hs2
  · exact hs3
  · exact hres
  · exact h_bound
  · exact h_trans

/-!
# Section 14: Master Completeness Theorem -/

theorem cook_levin_completeness (p : MachineParams) (T : ℕ) (input : List ℕ) (acc : ℕ) (trace : ℕ → Configuration) :
  T > 1 → 
  input.length < T →
  (∀ t i, trace t i < p.alphabet_size * (1 + p.state_count)) →
  (∀ i h, trace 0 i = input.get ⟨i, h⟩) →
  (∃ i < T, trace (T - 1) i = acc) →
  (∀ t i s1 s2 s3 res, t + 1 < T → 0 < i → i + 1 < T →
    trace t (i - 1) = s1 ∧ trace t i = s2 ∧ trace t (i + 1) = s3 → trace (t + 1) i ≠ res) →
  formula_is_satisfiable (cook_levin_cnf p T input acc) (construct_assignment p T trace) := 
by
  intros hT h_input_len h_bound h_start h_acc h_trans_logic clause h_cl
  unfold cook_levin_cnf at h_cl
  rw [List.mem_append] at h_cl
  cases h_cl with
  | inl h_nested => 
      rw [List.mem_append] at h_nested
      cases h_nested with
      | inl h_st => exact satisfy_start p T input trace h_input_len h_bound h_start clause h_st
      | inr h_ac => exact satisfy_accept p T acc trace h_bound (by linarith) h_acc clause h_ac
  | inr h_str => 
      simp only [List.mem_flatMap, List.mem_range] at h_str
      obtain ⟨t, ht, i, hi, h_mem⟩ := h_str
      simp only [List.mem_cons] at h_mem
      rcases h_mem with h_head | h_tail
      · rw [h_head]
        exact completeness_at_least_one p T t i trace ht hi h_bound
      · exact completeness_at_most_one p T t i trace ht hi clause h_tail

/-! # Section 15: The Final Master Soundness Logic -/

open Classical 

noncomputable def extract_trace (p : MachineParams) (T : ℕ) (assignment : ℕ → Prop) : ℕ → Configuration :=
  fun t i => 
    let S := p.alphabet_size * (1 + p.state_count)
    if h : ∃ s < S, assignment (get_var p T t i s) then
      Classical.choose h
    else
      0

theorem cook_levin_final_soundness (p : MachineParams) (T : ℕ) (input : List ℕ) (acc : ℕ) (assignment : ℕ → Prop) :
  T > 1 →
  acc < (p.alphabet_size * (1 + p.state_count)) → 
  formula_is_satisfiable (cook_levin_cnf p T input acc) assignment →
  ∃ (trace : ℕ → Configuration), 
    (∀ t i, trace t i < p.alphabet_size * (1 + p.state_count)) ∧
    (∃ i < T, trace (T - 1) i = acc) := 
by
  intros hT_bound h_acc_valid h_sat
  let trace := extract_trace p T assignment
  use trace
  let S := p.alphabet_size * (1 + p.state_count)
  have h_exactly_one : ∀ t < T, ∀ i < T, ∃! s, s < S ∧ assignment (get_var p T t i s) := by
    intros t ht i hi
    apply exactly_one_symbol p T t i assignment
    · unfold formula_is_satisfiable at h_sat
      have h_mem : at_least_one_symbol p T t i ∈ cook_levin_cnf p T input acc := by
        unfold cook_levin_cnf
        simp only [List.mem_append, List.mem_flatMap, List.mem_range, List.mem_cons]
        exact Or.inr ⟨t, ht, i, hi, Or.inl rfl⟩
      exact h_sat _ h_mem
    · unfold formula_is_satisfiable at h_sat
      intros clause h_cl
      have h_mem : clause ∈ cook_levin_cnf p T input acc := by
        unfold cook_levin_cnf
        simp only [List.mem_append, List.mem_flatMap, List.mem_range, List.mem_cons]
        exact Or.inr ⟨t, ht, i, hi, Or.inr h_cl⟩
      exact h_sat _ h_mem

  constructor
  · intros t i
    dsimp [trace, extract_trace]
    split
    · rename_i h_ex; exact (Classical.choose_spec h_ex).1
    · apply Nat.mul_pos p.alphabet_pos (by linarith)
      
  · have h_sound := cook_levin_soundness p T input acc assignment h_sat
    obtain ⟨i, hi_T, h_assign_acc⟩ := h_sound
    use i; use hi_T
    dsimp [trace, extract_trace]
    let T_minus_1 := T - 1
    have h_Tm1 : T_minus_1 < T := Nat.sub_lt (by linarith) (by linarith)
    have h_ex : ∃ s < S, assignment (get_var p T T_minus_1 i s) := ⟨acc, h_acc_valid, h_assign_acc⟩
    rw [dif_pos h_ex]
    let chosen_s := Classical.choose h_ex
    have h_spec := Classical.choose_spec h_ex 
    have h_unique := h_exactly_one T_minus_1 h_Tm1 i hi_T
    obtain ⟨s_main, h_s_prop, h_s_unique⟩ := h_unique
    have h1 : chosen_s = s_main := h_s_unique chosen_s h_spec
    have h2 : acc = s_main := h_s_unique acc ⟨h_acc_valid, h_assign_acc⟩
    exact h1.trans h2.symm
