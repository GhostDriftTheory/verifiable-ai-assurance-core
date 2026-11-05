import ResponsibilityOS
import adic_cyber_assurance_gateway
import Lean.Util.CollectAxioms

/-!
# Formal Foundations of Verifiable AI Assurance

A public, implementation-independent mathematical model of three complementary
assurance capabilities: evidence authenticity, execution assurance, and
responsibility traceability.

The goal predicate is supplied independently. Sufficiency requires an explicit
coverage hypothesis; this file does not derive that hypothesis from legislation.
Necessity is an information-separation result, not a claim that three products
or three software modules are uniquely required. A certificate could carry the
information for more than one capability.

Only abstract observations, finite logical counterexamples, history distinctions,
and corollaries of two already-public kernels are included. There is no runtime,
transaction format, evidence-binding protocol, verification algorithm, actuator,
state-update procedure, or integration adapter in this file.

The Gateway corollary concerns evidence for an accepted execution. It does not
establish that a real operation was prevented before execution. The responsibility
result concerns preservation of selected distinctions, not physical-world truth.
The policy scope does not assert complete EU AI Act or Hiroshima AI Process
compliance, cryptographic security, or safety of any particular implementation.
-/

set_option autoImplicit false
set_option Elab.async false

namespace VerifiableAIAssurance

/-! ## 1. A requirement independent of its observation mechanism -/

/-- Equal observations must not merge cases with different requirement outcomes. -/
def Sufficient {W V : Type} (view : W → V) (goal : W → Prop) : Prop :=
  ∀ x y, view x = view y → (goal x ↔ goal y)

/-- Mathematical exactness, not a proposed production decision procedure. -/
def ExactJudge {W V : Type} (view : W → V) (goal : W → Prop)
    (judge : V → Prop) : Prop :=
  ∀ w, judge (view w) ↔ goal w

/-- Necessary and sufficient information condition for exact judging.
The existential predicate constructed in this proof need not be computable. -/
theorem sufficient_iff_exact_judge {W V : Type}
    (view : W → V) (goal : W → Prop) :
    Sufficient view goal ↔ ∃ judge, ExactJudge view goal judge := by
  constructor
  · intro h
    refine ⟨fun observation => ∃ w, view w = observation ∧ goal w, ?_⟩
    intro w
    constructor
    · rintro ⟨x, hx, hg⟩
      exact (h x w hx).mp hg
    · intro hg
      exact ⟨w, rfl, hg⟩
  · rintro ⟨judge, hj⟩ x y heq
    calc
      goal x ↔ judge (view x) := (hj x).symm
      _ ↔ judge (view y) := by rw [heq]
      _ ↔ goal y := hj y

/-- Soundness plus ONE useful acceptance already requires a distinguishing view.
No completeness assumption is imposed on a commercial verifier. -/
theorem sound_useful_judge_must_separate {W V : Type}
    (view : W → V) (goal : W → Prop) (good bad : W)
    (badFails : ¬ goal bad) (judge : V → Prop)
    (sound : ∀ w, judge (view w) → goal w)
    (useful : judge (view good)) : view good ≠ view bad := by
  intro same
  apply badFails
  apply sound bad
  rw [← same]
  exact useful

/-! ## 2. Conditional composition on the SAME abstract case -/

/-- Observations only: no prescribed evidence schema or linking protocol. -/
def jointView {W A E R : Type}
    (origin : W → A) (execution : W → E) (responsibility : W → R)
    (w : W) : A × E × R :=
  (origin w, execution w, responsibility w)

/-- This explicit coverage obligation is NOT proved merely by naming three roles. -/
def Covers {W : Type} (goal authentic executed inspectable : W → Prop) : Prop :=
  ∀ w, goal w ↔ authentic w ∧ executed w ∧ inspectable w

/-- Independent local adequacy plus semantic coverage implies joint adequacy.
The same `w` is essential: separate facts about different cases do not suffice. -/
theorem covered_joint_view_is_sufficient {W A E R : Type}
    (origin : W → A) (execution : W → E) (responsibility : W → R)
    (goal authentic executed inspectable : W → Prop)
    (coverage : Covers goal authentic executed inspectable)
    (ho : Sufficient origin authentic)
    (he : Sufficient execution executed)
    (hr : Sufficient responsibility inspectable) :
    Sufficient (jointView origin execution responsibility) goal := by
  intro x y same
  have ao : authentic x ↔ authentic y :=
    ho x y (congrArg (fun z : A × E × R => z.1) same)
  have ae : executed x ↔ executed y :=
    he x y (congrArg (fun z : A × E × R => z.2.1) same)
  have ar : inspectable x ↔ inspectable y :=
    hr x y (congrArg (fun z : A × E × R => z.2.2) same)
  constructor
  · intro hx
    obtain ⟨a, e, r⟩ := (coverage x).mp hx
    exact (coverage y).mpr ⟨ao.mp a, ae.mp e, ar.mp r⟩
  · intro hy
    obtain ⟨a, e, r⟩ := (coverage y).mp hy
    exact (coverage x).mpr ⟨ao.mpr a, ae.mpr e, ar.mpr r⟩

/-- Three locally successful statements may concern no single successful case.
This is a logical counterexample, not a transaction-binding implementation. -/
theorem separate_local_successes_need_not_have_a_common_case :
    (∃ x : Bool, x = false) ∧
    (∃ x : Bool, x = true) ∧
    (∃ _x : Bool, True) ∧
    ¬ (∃ x : Bool, x = false ∧ x = true ∧ True) := by
  refine ⟨⟨false, rfl⟩, ⟨true, rfl⟩, ⟨false, True.intro⟩, ?_⟩
  rintro ⟨x, hf, ht, _⟩
  rw [hf] at ht
  cases ht

/-! ## 3. Non-vacuous, independent omission counterexamples
These four cases are semantic valuations, not verifier success flags. -/

namespace Independence

inductive Case where
  | acceptable
  | originFailure
  | executionFailure
  | responsibilityFailure
  deriving DecidableEq

inductive Capability where
  | origin
  | execution
  | responsibility
  deriving DecidableEq

def goal (w : Case) : Prop := w = .acceptable

def origin : Case → Bool
  | .originFailure => false
  | _ => true

def execution : Case → Bool
  | .executionFailure => false
  | _ => true

def responsibility : Case → Bool
  | .responsibilityFailure => false
  | _ => true

def without : Capability → Case → Bool × Bool
  | .origin, w => (execution w, responsibility w)
  | .execution, w => (origin w, responsibility w)
  | .responsibility, w => (origin w, execution w)

def failure : Capability → Case
  | .origin => .originFailure
  | .execution => .executionFailure
  | .responsibility => .responsibilityFailure

theorem coverage : Covers goal (fun w => origin w = true)
    (fun w => execution w = true) (fun w => responsibility w = true) := by
  intro w
  cases w <;> simp [goal, origin, execution, responsibility]

theorem acceptable_case_exists : ∃ w, goal w := ⟨.acceptable, rfl⟩

theorem omission_collision (c : Capability) :
    without c .acceptable = without c (failure c) ∧
    goal .acceptable ∧ ¬ goal (failure c) := by
  cases c <;> simp [without, failure, goal, origin, execution, responsibility]

/-- Every omitted capability forces a sound judge to reject this useful case. -/
theorem omission_prevents_sound_useful_acceptance (c : Capability)
    (judge : (Bool × Bool) → Prop)
    (sound : ∀ w, judge (without c w) → goal w) :
    ¬ judge (without c .acceptable) := by
  intro useful
  obtain ⟨same, _, bad⟩ := omission_collision c
  exact (sound_useful_judge_must_separate
    (without c) goal .acceptable (failure c) bad judge sound useful) same

theorem omitted_view_is_insufficient (c : Capability) :
    ¬ Sufficient (without c) goal := by
  intro h
  obtain ⟨same, good, bad⟩ := omission_collision c
  exact bad ((h .acceptable (failure c) same).mp good)

theorem combined_view_is_sufficient :
    Sufficient (jointView origin execution responsibility) goal := by
  apply covered_joint_view_is_sufficient origin execution responsibility
    goal (fun w => origin w = true) (fun w => execution w = true)
    (fun w => responsibility w = true) coverage
  · intro x y h
    change (origin x = true) ↔ (origin y = true)
    rw [h]
  · intro x y h
    change (execution x = true) ↔ (execution y = true)
    rw [h]
  · intro x y h
    change (responsibility x = true) ↔ (responsibility y = true)
    rw [h]

/-- Minimality is relative to deleting these observations on this case family.
It is not a minimum number of products, fields, or physical components. -/
theorem three_capability_information_result :
    (∃ w, goal w) ∧
    Sufficient (jointView origin execution responsibility) goal ∧
    (∀ c, ¬ Sufficient (without c) goal) :=
  ⟨acceptable_case_exists, combined_view_is_sufficient, omitted_view_is_insufficient⟩

end Independence

/-! ## 4. Direct connection to the published Responsibility OS policy
Ordered lists here are mathematical histories, not a log-storage design. -/

open CategoryTheory

structure TraceObject (A : Type) where
  token : Unit

instance traceCategory (A : Type) : Category (TraceObject A) where
  Hom _ _ := List A
  id _ := []
  comp f g := f ++ g
  id_comp := by intros; apply List.nil_append
  comp_id := by intros; apply List.append_nil
  assoc := by intros; apply List.append_assoc

def traceView {A B : Type} (view : A → B) :
    TraceObject A ⥤ TraceObject B where
  obj _ := ⟨()⟩
  map f := f.map view
  map_id _ := rfl
  map_comp := by
    intro X Y Z f g
    change List.map view ((show List A from f) ++ (show List A from g)) =
      List.map view (show List A from f) ++ List.map view (show List A from g)
    simp only [List.map_append]

def selectedPolicy {A S : Type} (summary : A → S) :
    ResponsibilityOS.ObservationPolicy (TraceObject A) where
  relevant f g := f.map summary ≠ g.map summary
  sound := by
    intro X Y f g h heq
    exact h (congrArg (List.map summary) heq)

/-- Retain whichever distinctions the chosen audit actually needs. -/
def PreservesDistinctions {A B S : Type} (view : A → B) (summary : A → S) : Prop :=
  ∀ x y, view x = view y → summary x = summary y

theorem list_map_preserves_selected_distinctions {A B S : Type}
    (view : A → B) (summary : A → S)
    (h : PreservesDistinctions view summary) :
    ∀ xs ys : List A, xs.map view = ys.map view →
      xs.map summary = ys.map summary := by
  intro xs
  induction xs with
  | nil =>
      intro ys heq
      cases ys with
      | nil => rfl
      | cons y ys => simp at heq
  | cons x xs ih =>
      intro ys heq
      cases ys with
      | nil => simp at heq
      | cons y ys =>
          have hh : view x = view y ∧ xs.map view = ys.map view := by
            simpa only [List.map_cons, List.cons.injEq] using heq
          simp only [List.map_cons, h x y hh.1, ih ys hh.2]

/-- The imported kernel policy holds on all finite histories exactly when
single-case observations preserve the selected distinctions. -/
theorem kernel_policy_iff_selected_distinctions {A B S : Type}
    (view : A → B) (summary : A → S) :
    ResponsibilityOS.PreservesPolicy (traceView view) (selectedPolicy summary) ↔
      PreservesDistinctions view summary := by
  constructor
  · intro hp x y hxy
    by_contra hne
    let o : TraceObject A := ⟨()⟩
    have relevant : (selectedPolicy summary).relevant
        (X := o) (Y := o) ([x] : List A) ([y] : List A) := by
      change [summary x] ≠ [summary y]
      intro heq
      exact hne (List.cons.inj heq).1
    have visibleNe := @hp o o ([x] : List A) ([y] : List A) relevant
    apply visibleNe
    change [view x] = [view y]
    rw [hxy]
  · intro h X Y f g relevant same
    change f.map summary ≠ g.map summary at relevant
    change f.map view = g.map view at same
    exact relevant (list_map_preserves_selected_distinctions view summary h f g same)

/-- Mathematical event composition preserves the selected goal distinctions.
This does not establish distributed-runtime enforcement or legal accountability. -/
theorem joint_information_preserves_selected_history {W A E R : Type}
    (origin : W → A) (execution : W → E) (responsibility : W → R)
    (goal authentic executed inspectable : W → Prop)
    (coverage : Covers goal authentic executed inspectable)
    (ho : Sufficient origin authentic) (he : Sufficient execution executed)
    (hr : Sufficient responsibility inspectable) :
    ResponsibilityOS.PreservesPolicy
      (traceView (jointView origin execution responsibility)) (selectedPolicy goal) := by
  apply (kernel_policy_iff_selected_distinctions _ _).mpr
  intro x y same
  exact propext ((covered_joint_view_is_sufficient origin execution responsibility
    goal authentic executed inspectable coverage ho he hr) x y same)

/-! ## 5. Corollaries of the already-public Gateway -- no new adapter
The imported trust assumptions remain in force. These corollaries do not prove
that external credentials, hardware, or a production runtime satisfy the model. -/

namespace PublicGateway

theorem published_commit_yields_execution_evidence
    (before after : ADIC.State) (ledger : ADIC.Ledger)
    (pre post : ADIC.LedgerEntry) (preRecord record : ADIC.EvidenceRecord)
    (h : ADIC.CommittedByLedger before after ledger pre post preRecord record) :
    ∃ w : ADIC.ADICWitness,
      ADIC.ValidADICWitness w ∧ w.before = before ∧ w.after = after ∧
      w.record = record ∧ ADIC.Sem record.operation before after ∧
      ADIC.EffectLe (ADIC.Eff record.operation before after) record.phi := by
  obtain ⟨w, hw, hb, ha, _, _, _, _, hr⟩ :=
    ADIC.committed_transition_yields_witness
      before after ledger pre post preRecord record h
  refine ⟨w, hw, hb, ha, hr, ?_, ?_⟩
  · simpa only [hb, ha, hr] using ADIC.valid_witness_has_semantic_execution w hw
  · simpa only [hb, ha, hr] using ADIC.valid_witness_effect_is_within_phi w hw

/-- Non-vacuity uses the published kernel's example, not a new execution model. -/
theorem published_execution_evidence_is_nonempty :
    ∃ w : ADIC.ADICWitness, ADIC.ValidADICWitness w := by
  obtain ⟨before, after, ledger, pre, post, preRecord, record, h⟩ :=
    ADIC.NonVacuity.committed_by_ledger_nonempty
  obtain ⟨w, hw, _, _, _, _, _⟩ :=
    published_commit_yields_execution_evidence
      before after ledger pre post preRecord record h
  exact ⟨w, hw⟩

end PublicGateway

/-! ## 6. Explicit information boundary -/

/-- An extra requirement that differs between indistinguishable cases needs
additional information. No claim that this profile settles every safety duty. -/
theorem independent_requirement_needs_more_information {W V : Type}
    (view : W → V) (requirement : W → Prop) (x y : W)
    (same : view x = view y) (hx : requirement x) (hy : ¬ requirement y) :
    ¬ ∃ judge, ExactJudge view requirement judge := by
  intro h
  have hs := (sufficient_iff_exact_judge view requirement).mpr h
  exact hy ((hs x y same).mp hx)

/-- Separately represented, irrelevant information is not needed for judging.
This is functional independence, not zero-knowledge or unlinkability security. -/
theorem irrelevant_information_need_not_be_disclosed {W V H : Type}
    (view : W → V) (goal : W → Prop) (h : Sufficient view goal) :
    Sufficient (fun p : W × H => view p.1) (fun p => goal p.1) := by
  intro x y same
  exact h x.1 y.1 same

end VerifiableAIAssurance

/-! Reject every unlisted proof dependency. The pure theory is allowed only
ordinary Lean logical axioms. Only the two PublicGateway corollaries may also
use the individually listed assumptions of the already-public Gateway. -/
run_cmd do
  let ordinary : List Lean.Name := [`propext, `Classical.choice, `Quot.sound]
  let upstream : List Lean.Name :=
    [`ADIC.TCB.digest_state, `ADIC.TCB.digest_operation,
     `ADIC.TCB.digest_phi, `ADIC.TCB.digest_decision,
     `ADIC.TCB.digest_approval, `ADIC.TCB.digest_obligations,
     `ADIC.TCB.digest_entry_body, `ADIC.TCB.signature_valid, `ADIC.TCB.time_valid]
  let env ← Lean.getEnv
  let mut audited : Nat := 0
  for (name, info) in env.constants.toList do
    if (`VerifiableAIAssurance).isPrefixOf name then
      match info with
      | .thmInfo _ =>
          let allowed := if (`VerifiableAIAssurance.PublicGateway).isPrefixOf name
            then ordinary ++ upstream else ordinary
          let dependencies ← Lean.collectAxioms name
          Lean.logInfo m!"AUDIT {name}"
          for dependency in dependencies do
            unless allowed.contains dependency do
              Lean.throwError m!"Axiom audit failed: {name} depends on {dependency}"
            Lean.logInfo m!"  {dependency}"
          audited := audited + 1
      | .axiomInfo _ =>
          Lean.throwError m!"New axiom forbidden in public theory: {name}"
      | _ => pure ()
  if audited == 0 then
    Lean.throwError "Axiom audit failed: no target theorems were found"
  Lean.logInfo m!"Axiom whitelist checked for {audited} theorems."
