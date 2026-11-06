import ResponsibilityOS
import adic_cyber_assurance_gateway
import Lean.Util.CollectAxioms

/-!
# Formal Foundations of Verifiable AI Assurance

A public, implementation-independent mathematical model of three complementary
assurance capabilities: evidence authenticity, execution assurance, and
responsibility traceability.

The central results start from externally selected requirements and the complete
available observation, not a three-part product model. They separate information
adequacy from the soundness of an actual check. A policy example grounded in
RFC 9334 instantiates the general results. Corollaries of the existing public
Gateway discharge an external resource policy and connect its published records
to the Responsibility OS history policy. The old four-case independence example
is an illustration only. Existing sufficient or redundant information is
explicitly supported; no result here singles out a required vendor, proprietary
technology, or number of products.

The goal predicate is supplied independently. Sufficiency for a combined goal
requires an explicit coverage hypothesis; this file does not derive that
hypothesis, the admissible worlds, or observation fidelity from legislation.
Necessity is an information-separation result, not a claim that three products
or three software modules are uniquely required. A certificate could carry the
information for more than one capability.

Only abstract observations, finite logical counterexamples, history distinctions,
and corollaries of two already-public kernels are included. There is no runtime,
transaction format, evidence-binding protocol, production verification algorithm, actuator,
state-update procedure, or integration adapter in this file.

The original Gateway corollary concerns evidence for an accepted execution. Its
input includes semantic and effect conditions, not only ledger membership. It does not
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

/-! ## 3. Requirement-led information conditions

`W` denotes the independently justified admissible case domain. It may be a
subtype restricting a larger mathematical model. `view` must contain ALL
information available to the proposed judge, not just a convenient subset.
`goal` and the selected requirements must be fixed independently of the view.

Cases must include the possibilities compatible with the available evidence,
not just a finite log whose rows have unique IDs.

No finite counterexample, product decomposition, capability count, independence
of failure modes, or vendor-specific property is assumed by these results.
The existence and admissibility of a real conflicting pair are application
obligations, NOT consequences of citing a standard or naming three capabilities.
-/

namespace Requirements

/-- An acceptable and an unacceptable case with exactly the same observation.
This is a logical proposition, not a prescribed evidence or transaction format. -/
def Conflict {W V : Type} (view : W → V) (goal : W → Prop) : Prop :=
  ∃ good bad, view good = view bad ∧ goal good ∧ ¬ goal bad

/-- A conflicting pair is necessary AND sufficient for information inadequacy.
The pair must belong to the chosen admissible domain `W`. -/
theorem insufficient_iff_conflict {W V : Type}
    (view : W → V) (goal : W → Prop) :
    ¬ Sufficient view goal ↔ Conflict view goal := by
  classical
  constructor
  · intro insufficient
    by_contra noConflict
    apply insufficient
    intro x y same
    constructor
    · intro good
      by_contra bad
      exact noConflict ⟨x, y, same, good, bad⟩
    · intro good
      by_contra bad
      exact noConflict ⟨y, x, same.symm, good, bad⟩
  · rintro ⟨good, bad, same, goodPasses, badFails⟩ sufficient
    exact badFails ((sufficient good bad same).mp goodPasses)

/-- Exact criterion for accepting ONE specified case without any false acceptance.
No requirement to accept every good case, and no computability claim. -/
theorem sound_useful_at_iff_no_bad_collision {W V : Type}
    (view : W → V) (goal : W → Prop) (good : W) :
    (∃ judge : V → Prop,
      (∀ w, judge (view w) → goal w) ∧ judge (view good)) ↔
    (∀ w, view w = view good → goal w) := by
  constructor
  · rintro ⟨judge, sound, useful⟩ w same
    apply sound w
    rw [same]
    exact useful
  · intro safe
    refine ⟨fun v => v = view good, ?_, rfl⟩
    intro w same
    exact safe w same

/-- A standard or policy may motivate `goal`; it does not establish this witness.
Once supplied, the witness rules out sound acceptance of its good case. -/
theorem conflict_blocks_sound_acceptance {W V : Type}
    (view : W → V) (goal : W → Prop) (good bad : W)
    (same : view good = view bad) (badFails : ¬ goal bad)
    (judge : V → Prop) (sound : ∀ w, judge (view w) → goal w) :
    ¬ judge (view good) := by
  intro useful
  exact (sound_useful_judge_must_separate
    view goal good bad badFails judge sound useful) same

/-- Additional observations suffice exactly when they separate EVERY remaining
acceptable/unacceptable pair. Separating one hand-picked example is not enough.
No individual adequacy or independence assumption is imposed on either view. -/
theorem joint_sufficient_iff_resolves_conflicts {W B A : Type}
    (base : W → B) (additional : W → A) (goal : W → Prop) :
    Sufficient (fun w => (base w, additional w)) goal ↔
    (∀ good bad, base good = base bad → goal good → ¬ goal bad →
      additional good ≠ additional bad) := by
  classical
  constructor
  · intro sufficient good bad same goodPasses badFails sameAdditional
    exact badFails ((sufficient good bad (Prod.ext same sameAdditional)).mp goodPasses)
  · intro resolves x y same
    have sameBase : base x = base y := congrArg Prod.fst same
    have sameAdditional : additional x = additional y := congrArg Prod.snd same
    constructor
    · intro good
      by_contra bad
      exact (resolves x y sameBase good bad) sameAdditional
    · intro good
      by_contra bad
      exact (resolves y x sameBase.symm good bad) sameAdditional.symm

/-- Existing adequate information remains adequate after adjoining other evidence.
This expressly permits the conclusion that no new assurance source is needed. -/
theorem existing_sufficiency_is_preserved {W B A : Type}
    (base : W → B) (additional : W → A) (goal : W → Prop)
    (sufficient : Sufficient base goal) :
    Sufficient (fun w => (base w, additional w)) goal := by
  intro x y same
  exact sufficient x y (congrArg Prod.fst same)

/-- Formatting, relabelling, or deterministic computation on the same available
information cannot remove an information-theoretic inability to judge. -/
theorem postprocessing_cannot_create_sufficiency {W V U : Type}
    (view : W → V) (transform : V → U) (goal : W → Prop)
    (sufficient : Sufficient (fun w => transform (view w)) goal) :
    Sufficient view goal := by
  intro x y same
  exact sufficient x y (congrArg transform same)

/-- A purported extra source reconstructible from the base is informationally
redundant for this goal. Raw data not present in `base` would be new information. -/
theorem reconstructible_addition_is_redundant {W B A : Type}
    (base : W → B) (additional : W → A) (goal : W → Prop)
    (reconstruct : B → A) (derived : ∀ w, additional w = reconstruct (base w)) :
    Sufficient (fun w => (base w, additional w)) goal ↔ Sufficient base goal := by
  constructor
  · intro sufficient x y same
    apply sufficient x y
    apply Prod.ext same
    calc
      additional x = reconstruct (base x) := derived x
      _ = reconstruct (base y) := congrArg reconstruct same
      _ = additional y := (derived y).symm
  · exact existing_sufficiency_is_preserved base additional goal

/-- An exact criterion for strict informational complementarity, relative to
a fixed goal and admissible cases: the baseline really lacks information, and the combination removes ALL
of its relevant ambiguities. No product or vendor is singled out. -/
theorem strict_complementarity_iff {W B A : Type}
    (base : W → B) (additional : W → A) (goal : W → Prop) :
    (¬ Sufficient base goal ∧
      Sufficient (fun w => (base w, additional w)) goal) ↔
    (Conflict base goal ∧
      ∀ good bad, base good = base bad → goal good → ¬ goal bad →
        additional good ≠ additional bad) := by
  constructor
  · rintro ⟨inadequate, adequateJoint⟩
    exact ⟨(insufficient_iff_conflict base goal).mp inadequate,
      (joint_sufficient_iff_resolves_conflicts base additional goal).mp adequateJoint⟩
  · rintro ⟨conflict, resolves⟩
    exact ⟨(insufficient_iff_conflict base goal).mpr conflict,
      (joint_sufficient_iff_resolves_conflicts base additional goal).mpr resolves⟩

/-- Selected requirements need not number three and need not be independent.
Preserving only the overall pass/fail verdict may be weaker than this obligation. -/
def FamilySufficient {W V I : Type}
    (view : W → V) (requirements : I → W → Prop) : Prop :=
  ∀ i, Sufficient view (requirements i)

/-- Every selected requirement is separately judgeable from the same observation.
The existential predicates are not supplied as executable verification code. -/
theorem family_sufficient_iff_exact_judges {W V I : Type}
    (view : W → V) (requirements : I → W → Prop) :
    FamilySufficient view requirements ↔
      ∀ i, ∃ judge, ExactJudge view (requirements i) judge := by
  constructor
  · intro sufficient i
    exact (sufficient_iff_exact_judge view (requirements i)).mp (sufficient i)
  · intro judges i
    exact (sufficient_iff_exact_judge view (requirements i)).mpr (judges i)

/-- Complementarity is checked against each selected requirement, including
requirements whose failure reasons are hidden by an overall rejected verdict. -/
theorem family_joint_iff_resolves_conflicts {W B A I : Type}
    (base : W → B) (additional : W → A) (requirements : I → W → Prop) :
    FamilySufficient (fun w => (base w, additional w)) requirements ↔
      ∀ i good bad, base good = base bad → requirements i good →
        ¬ requirements i bad → additional good ≠ additional bad := by
  constructor
  · intro sufficient i
    exact (joint_sufficient_iff_resolves_conflicts base additional (requirements i)).mp
      (sufficient i)
  · intro resolves i
    exact (joint_sufficient_iff_resolves_conflicts base additional (requirements i)).mpr
      (resolves i)

/-- Coverage is an explicit, externally justified application obligation.
This theorem does not infer complete legal or operational coverage from a list. -/
theorem covered_requirements_give_goal_sufficiency {W V I : Type}
    (view : W → V) (requirements : I → W → Prop) (goal : W → Prop)
    (coverage : ∀ w, goal w ↔ ∀ i, requirements i w)
    (sufficient : FamilySufficient view requirements) : Sufficient view goal := by
  intro x y same
  constructor
  · intro good
    apply (coverage y).mpr
    intro i
    exact (sufficient i x y same).mp ((coverage x).mp good i)
  · intro good
    apply (coverage x).mpr
    intro i
    exact (sufficient i x y same).mpr ((coverage y).mp good i)

/-- Removing impossible cases can remove a counterexample. An impossibility
claim therefore has to use witnesses INSIDE the justified admissible domain. -/
theorem sufficiency_restricts_to_admissible_cases {W V : Type}
    (admissible : W → Prop) (view : W → V) (goal : W → Prop)
    (sufficient : Sufficient view goal) :
    Sufficient (fun w : {w // admissible w} => view w.val)
      (fun w => goal w.val) := by
  intro x y same
  exact sufficient x.val y.val same

/-- The stated correspondences are SUFFICIENT to transfer the result. They
are not claimed to be necessary for every fixed goal. Neither correspondence
is established by a citation alone. -/
theorem sufficiency_transfers_with_faithful_abstraction {W M V U : Type}
    (actual : W → V) (abstraction : W → M) (modeled : M → U)
    (actualGoal : W → Prop) (modelGoal : M → Prop)
    (observations : ∀ x y, actual x = actual y → modeled (abstraction x) = modeled (abstraction y))
    (requirements : ∀ w, actualGoal w ↔ modelGoal (abstraction w))
    (sufficient : Sufficient modeled modelGoal) : Sufficient actual actualGoal := by
  intro x y same
  exact (requirements x).trans
    ((sufficient (abstraction x) (abstraction y) (observations x y same)).trans
      (requirements y).symm)

/-- Necessity transfer needs actual witnesses and the OPPOSITE observation
implication: model equality must not hide extra information in the real system.
This prevents transferring a toy collision to a richer production observation. -/
theorem realized_conflict_transfers {W M V U : Type}
    (actual : W → V) (abstraction : W → M) (modeled : M → U)
    (actualGoal : W → Prop) (modelGoal : M → Prop)
    (observations : ∀ x y, modeled (abstraction x) = modeled (abstraction y) → actual x = actual y)
    (requirements : ∀ w, actualGoal w ↔ modelGoal (abstraction w))
    (good bad : W) (same : modeled (abstraction good) = modeled (abstraction bad))
    (goodPasses : modelGoal (abstraction good)) (badFails : ¬ modelGoal (abstraction bad)) :
    Conflict actual actualGoal := by
  refine ⟨good, bad, observations good bad same, (requirements good).mpr goodPasses, ?_⟩
  intro passes
  exact badFails ((requirements bad).mp passes)

/-- A nonconstant goal can be settled by ONE observation. This regression guards
against interpreting the three-capability illustration as a universal minimum. -/
theorem one_observation_can_suffice :
    Sufficient (fun b : Bool => b) (fun b => b = true) ∧
      ¬ Sufficient (fun _b : Bool => ()) (fun b => b = true) := by
  constructor
  · intro x y same
    change x = y at same
    change (x = true ↔ y = true)
    rw [same]
  · intro sufficient
    have impossible : (false : Bool) = true :=
      (sufficient true false rfl).mp rfl
    cases impossible

/-- Exact overall decisions alone need not preserve explanations of failures.
This nonconstant Boolean regression has a successful case; it is not an
application model or a premise about real deployments. -/
theorem verdict_sufficiency_need_not_preserve_each_requirement :
    (∃ w : Bool × Bool, w.1 = true ∧ w.2 = true) ∧
    Sufficient (fun w : Bool × Bool => w.1 && w.2)
      (fun w => (w.1 && w.2) = true) ∧
    ¬ Sufficient (fun w : Bool × Bool => w.1 && w.2)
      (fun w => w.1 = true) := by
  refine ⟨⟨(true, true), rfl, rfl⟩, ?_, ?_⟩
  · intro x y same
    change (x.1 && x.2) = (y.1 && y.2) at same
    change ((x.1 && x.2) = true) ↔ ((y.1 && y.2) = true)
    rw [same]
  · intro sufficient
    have impossible : (false : Bool) = true :=
      (sufficient (true, false) (false, false) rfl).mp rfl
    cases impossible

end Requirements

/-! ## 3a. Evidence-compatible possibilities, not just a list of recorded IDs

These are logical relations only. No evidence format or verification procedure
is specified. A compatibility relation must cover the actual admissible cases;
a catalogue with one row per observed identifier is not a justification for it.
-/
namespace EvidenceScope

/-- Sufficient premises for soundness: accepted evidence supports the goal in
every compatible admissible case, and the actual case is among those possibilities.
The correctness of the check is an obligation, not inferred from its existence. -/
theorem checked_compatible_evidence_is_sound {W V : Type}
    (view : W → V) (compatible : V → W → Prop) (goal : W → Prop)
    (check : V → Prop)
    (coversActual : ∀ w, compatible (view w) w)
    (checked : ∀ v, check v → ∀ w, compatible v w → goal w) :
    ∀ w, check (view w) → goal w := by
  intro w accepted
  exact checked (view w) accepted w (coversActual w)

/-- An acceptable label cannot repair evidence that remains compatible with a
failing case. This is not a statement about a particular deployed system. -/
theorem incompatible_goal_blocks_sound_check {W V : Type}
    (compatible : V → W → Prop) (goal : W → Prop) (check : V → Prop)
    (checked : ∀ v, check v → ∀ w, compatible v w → goal w)
    (v : V) (bad : W) (possible : compatible v bad) (fails : ¬ goal bad) :
    ¬ check v := by
  intro accepted
  exact fails (checked v accepted bad possible)

/-- Two alternative states of the SAME identified subject are allowed here.
This does not assert that two simultaneously existing devices share an ID.
Unique row IDs alone do not establish the truth of an unobserved fact. -/
theorem same_identifier_can_leave_a_conflict {Id : Type} (identifier : Id) :
    Requirements.Conflict (fun w : Id × Bool => w.1) (fun w => w.2 = true) := by
  refine ⟨(identifier, true), (identifier, false), rfl, rfl, ?_⟩
  intro impossible
  cases impossible

end EvidenceScope

/-! ## 3b. Source-grounded policy example: RFC 9334, section 8.2

The source distinguishes healthy devices from devices an enterprise owns.
`Case` is a semantic valuation of health and ownership, NOT a message schema.
The manufacturer is fixed. All four valuations are included; no independence
or missing capability of an actual vendor is asserted. True facts are used in
this example; authenticating the corresponding evidence remains a separate duty.
The selected policy is given as a proposition, independently of the Boolean check.
-/
namespace RFC9334

abbrev Case := Bool × Bool

def policy (w : Case) : Prop := w.1 = true ∧ w.2 = true

/-- A Boolean expression for the public example, not a production verifier. -/
def policyCheck (w : Case) : Bool := w.1 && w.2

/-- Health without ownership cannot settle this selected policy. The witnesses
are possible valuations in the source's example, not measured deployment data. -/
theorem health_only_is_insufficient :
    ¬ Sufficient (fun w : Case => w.1) policy := by
  apply (Requirements.insufficient_iff_conflict _ _).mpr
  refine ⟨(true, true), (true, false), rfl, ⟨rfl, rfl⟩, ?_⟩
  intro passes
  cases passes.2

/-- The concrete check matches the independently stated policy on ALL valuations,
not only on a selected successful example. -/
theorem policy_check_exact :
    ExactJudge (fun w : Case => w) policy (fun v => policyCheck v = true) := by
  intro w
  rcases w with ⟨healthy, owned⟩
  cases healthy <;> cases owned <;> simp [policy, policyCheck]

/-- The general information theorem is instantiated, not merely named. -/
theorem full_observation_is_sufficient :
    Sufficient (fun w : Case => w) policy := by
  exact (sufficient_iff_exact_judge _ _).mpr ⟨_, policy_check_exact⟩

/-- BOTH facts are available to this judge, but it uses only health.
Thus sufficient input does not make every implemented judgement sound. -/
theorem health_only_check_on_full_evidence_is_unsound :
    ¬ (∀ w : Case, w.1 = true → policy w) := by
  intro sound
  have impossible : (false : Bool) = true := (sound (true, false) rfl).2
  cases impossible

/-- Correct checking is useful without becoming a new information source. -/
theorem correct_check_adds_no_new_information :
    Sufficient (fun w : Case => (w, policyCheck w)) policy ↔
      Sufficient (fun w : Case => w) policy := by
  exact Requirements.reconstructible_addition_is_redundant
    (fun w : Case => w) policyCheck policy policyCheck (fun _ => rfl)

/-- Non-vacuity and the discriminating negative case use the SAME full inputs. -/
theorem policy_check_accepts_and_rejects :
    policyCheck (true, true) = true ∧
    policyCheck (true, false) = false ∧
    policy (true, true) ∧ ¬ policy (true, false) := by
  simp [policy, policyCheck]

/-- Ownership may already be recoverable from existing information. There is
then no argument for a new source or a new vendor based on this example. -/
theorem existing_ownership_information_is_enough {V : Type}
    (existing : Case → V) (recoverOwnership : V → Bool)
    (faithful : ∀ w, recoverOwnership (existing w) = w.2) :
    Sufficient (fun w => (w.1, existing w)) policy := by
  intro x y same
  change (x.1, existing x) = (y.1, existing y) at same
  have health : x.1 = y.1 := congrArg (fun p : Bool × V => p.1) same
  have source : existing x = existing y := congrArg (fun p : Bool × V => p.2) same
  have ownership : x.2 = y.2 :=
    (faithful x).symm.trans ((congrArg recoverOwnership source).trans (faithful y))
  change (x.1 = true ∧ x.2 = true) ↔ (y.1 = true ∧ y.2 = true)
  rw [health, ownership]

end RFC9334

/-! ## 4. Finite illustration ONLY -- not a justification of real premises
These four valuations demonstrate a possibility, not universal necessity.
The requirement-led theorems above do not depend on this namespace.
No inference about an actual system is licensed without admissible witnesses
and its complete observation model. The example is retained for regression. -/

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

/-! ## 5. Direct connection to the published Responsibility OS policy
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

/-- Preserve each selected requirement's truth distinction throughout a finite
history, not just the combined pass/fail result. This is mathematical mapping,
not log integrity, retention, actor attribution, or a storage implementation. -/
theorem requirement_family_preserves_selected_history {W V I : Type}
    (view : W → V) (requirements : I → W → Prop)
    (sufficient : Requirements.FamilySufficient view requirements) :
    ResponsibilityOS.PreservesPolicy (traceView view)
      (selectedPolicy (fun w i => requirements i w)) := by
  apply (kernel_policy_iff_selected_distinctions _ _).mpr
  intro x y same
  funext i
  exact propext (sufficient i x y same)

/-! ## 6. Corollaries of the already-public Gateway -- no new adapter
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

/-! ## 6a. Applying the PUBLIC Gateway contract to an external resource policy

Only logical corollaries of the pinned public definitions follow. No new
runtime, checker, execution gate, protocol, or adapter is introduced.

The write/delete policy is supplied independently. `AllowCore` supplies the
public authorization contract and a conservative effect bound. Its truth is
NOT inferred from an AI label, a signed record, or a stored "committed" flag.
`Sem` is the separately stated correspondence with the public operation model.
In particular this proof does not assume its external-policy conclusion.
-/

/-- A selected resource policy, not a complete security or legal specification.
The policy sets must be fixed by the relying organization, not chosen after
observing the actual effect merely to make the theorem apply. -/
def ExternalResourcePolicy (writes deletes : ADIC.Resource → Prop)
    (operation : ADIC.OperationRequest) (before after : ADIC.State) : Prop :=
  ADIC.AuthorityAllows operation before ∧
    (∀ r, (ADIC.Eff operation before after).writeSet r → writes r) ∧
    (∀ r, (ADIC.Eff operation before after).deleteSet r → deletes r)

/-- A concrete connection to the existing public contract: authorized actor,
conservative effect bound, policy-contained bound, and model-corresponding
execution imply the independently selected resource policy. `CommittedByLedger`
is deliberately NOT a premise of this theorem. -/
theorem published_allow_core_respects_external_resource_policy
    (operation : ADIC.OperationRequest) (before after : ADIC.State)
    (phi : ADIC.EffectBound) (approval : Option ADIC.Approval)
    (obligations : ADIC.VerificationObligations) (subjectDigest : ADIC.Digest)
    (atTime : ADIC.Time) (writes deletes : ADIC.Resource → Prop)
    (writeBound : ∀ r, phi.writeSet r → writes r)
    (deleteBound : ∀ r, phi.deleteSet r → deletes r)
    (allowed : ADIC.AllowCore operation before phi approval obligations subjectDigest atTime)
    (execution : ADIC.Sem operation before after) :
    ExternalResourcePolicy writes deletes operation before after := by
  rcases allowed with ⟨_identity, authority, overapprox, _risk, _approval, _path⟩
  have bounded := ADIC.committed_effect_within_phi
    before after operation phi execution overapprox
  exact ⟨authority,
    (fun r changed => writeBound r (bounded.2.1 r changed)),
    (fun r changed => deleteBound r (bounded.2.2.1 r changed))⟩

/-- The negative direction is a logical exclusion, NOT proof of real-world
pre-execution blocking. All original premises, including `Sem`, remain visible. -/
theorem external_policy_violation_excludes_allow_core
    (operation : ADIC.OperationRequest) (before after : ADIC.State)
    (phi : ADIC.EffectBound) (approval : Option ADIC.Approval)
    (obligations : ADIC.VerificationObligations) (subjectDigest : ADIC.Digest)
    (atTime : ADIC.Time) (writes deletes : ADIC.Resource → Prop)
    (writeBound : ∀ r, phi.writeSet r → writes r)
    (deleteBound : ∀ r, phi.deleteSet r → deletes r)
    (execution : ADIC.Sem operation before after)
    (violation : ¬ ExternalResourcePolicy writes deletes operation before after) :
    ¬ ADIC.AllowCore operation before phi approval obligations subjectDigest atTime := by
  intro allowed
  exact violation (published_allow_core_respects_external_resource_policy
    operation before after phi approval obligations subjectDigest atTime
    writes deletes writeBound deleteBound allowed execution)

/-- Reuses the already-published read-only example and its public lemmas.
No new operation, protected-resource example, or implementation is disclosed. -/
theorem published_read_example_satisfies_allow_core :
    ADIC.AllowCore ADIC.NonVacuity.concreteOperation ADIC.NonVacuity.concreteBefore
      ADIC.NonVacuity.concretePhi none ADIC.NonVacuity.concreteObligations
      "subject:demo" 1 := by
  refine ⟨?_, ?_, ADIC.NonVacuity.concrete_phi_overapprox, ?_, ?_,
    ADIC.NonVacuity.concrete_execution_path_bound⟩
  · simp [ADIC.IdentityValid, ADIC.NonVacuity.concreteOperation]
  · simp [ADIC.AuthorityAllows, ADIC.NonVacuity.concreteOperation,
      ADIC.NonVacuity.concreteBefore]
  · rw [ADIC.NonVacuity.concrete_risk_low]
    intro impossible
    cases impossible
  · unfold ADIC.ApprovalPolicyValidAt ADIC.SubjectFor ADIC.ApprovalValid
    simp [ADIC.NonVacuity.concrete_risk_low, ADIC.ApprovalPolicy]

/-- A positive instance of the external policy: the existing read-only example
is allowed with a policy permitting NO writes or deletes. This establishes
logical non-vacuity, not a new deployment or a benchmark. -/
theorem published_read_example_satisfies_external_policy :
    ExternalResourcePolicy (fun _ => False) (fun _ => False)
      ADIC.NonVacuity.concreteOperation ADIC.NonVacuity.concreteBefore
      ADIC.NonVacuity.concreteAfter := by
  apply published_allow_core_respects_external_resource_policy
    ADIC.NonVacuity.concreteOperation ADIC.NonVacuity.concreteBefore
    ADIC.NonVacuity.concreteAfter ADIC.NonVacuity.concretePhi none
    ADIC.NonVacuity.concreteObligations "subject:demo" 1
    (fun _ => False) (fun _ => False)
  · intro r changed
    exact changed
  · intro r changed
    exact changed
  · exact published_read_example_satisfies_allow_core
  · exact ADIC.NonVacuity.concrete_sem

/-- A mathematical selection of ALREADY-PUBLIC record fields. This is NOT a
new serialized record, packet format, logging design, or identity attestation.
The selected facts do not include every item required by NIST AU-3. -/
def selectedPublicAuditFacts (record : ADIC.EvidenceRecord) :=
  (record.operation.actor, record.operation.operation, record.operation.target,
    record.decision.policyVersion, record.result)

/-- The observation is the existing full record, not just a success label.
This directly instantiates the selected-distinction theory with the Gateway's
published record type. No validity, integrity, or physical truth follows from
field preservation alone. All candidate witnesses, not only valid ones, occur. -/
theorem published_record_preserves_selected_audit_history :
    ResponsibilityOS.PreservesPolicy
      (traceView (fun w : ADIC.ADICWitness => w.record))
      (selectedPolicy (fun w => selectedPublicAuditFacts w.record)) := by
  apply (kernel_policy_iff_selected_distinctions _ _).mpr
  intro x y same
  exact congrArg selectedPublicAuditFacts same

/-- A direct requirement-family instance on all public candidate witnesses.
Queries are predicates over the published record; this does not claim that
record fields alone determine arbitrary physical or legal requirements. -/
theorem published_record_is_sufficient_for_selected_record_questions {I : Type}
    (questions : I → ADIC.EvidenceRecord → Prop) :
    Requirements.FamilySufficient (fun w : ADIC.ADICWitness => w.record)
      (fun i w => questions i w.record) := by
  intro i x y same
  change x.record = y.record at same
  change questions i x.record ↔ questions i y.record
  rw [same]

/-- The two published kernels are actually connected: per-record questions
instantiate the general information criterion and its history theorem. -/
theorem published_record_questions_preserve_history {I : Type}
    (questions : I → ADIC.EvidenceRecord → Prop) :
    ResponsibilityOS.PreservesPolicy
      (traceView (fun w : ADIC.ADICWitness => w.record))
      (selectedPolicy (fun w i => questions i w.record)) := by
  exact requirement_family_preserves_selected_history
    (fun w : ADIC.ADICWitness => w.record) (fun i w => questions i w.record)
    (published_record_is_sufficient_for_selected_record_questions questions)

end PublicGateway

/-! ## 7. Explicit information boundary -/

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
ordinary Lean logical axioms. Only the PublicGateway corollaries may also
use the individually listed assumptions of the already-public Gateway. -/
run_cmd do
  let ordinary : List Lean.Name := [`propext, `Classical.choice, `Quot.sound]
  let upstream : List Lean.Name :=
    [`ADIC.TCB.digest_state, `ADIC.TCB.digest_operation,
     `ADIC.TCB.digest_phi, `ADIC.TCB.digest_decision,
     `ADIC.TCB.digest_approval, `ADIC.TCB.digest_obligations,
     `ADIC.TCB.digest_entry_body, `ADIC.TCB.signature_valid, `ADIC.TCB.time_valid]
  let env ← Lean.getEnv
  let required : List Lean.Name :=
    [`VerifiableAIAssurance.sufficient_iff_exact_judge,
     `VerifiableAIAssurance.Requirements.insufficient_iff_conflict,
     `VerifiableAIAssurance.Requirements.sound_useful_at_iff_no_bad_collision,
     `VerifiableAIAssurance.Requirements.joint_sufficient_iff_resolves_conflicts,
     `VerifiableAIAssurance.Requirements.strict_complementarity_iff,
     `VerifiableAIAssurance.Requirements.reconstructible_addition_is_redundant,
     `VerifiableAIAssurance.Requirements.family_joint_iff_resolves_conflicts,
     `VerifiableAIAssurance.Requirements.sufficiency_transfers_with_faithful_abstraction,
     `VerifiableAIAssurance.Requirements.realized_conflict_transfers,
     `VerifiableAIAssurance.Requirements.one_observation_can_suffice,
     `VerifiableAIAssurance.Requirements.verdict_sufficiency_need_not_preserve_each_requirement,
     `VerifiableAIAssurance.requirement_family_preserves_selected_history,
     `VerifiableAIAssurance.PublicGateway.published_commit_yields_execution_evidence,
     `VerifiableAIAssurance.EvidenceScope.checked_compatible_evidence_is_sound,
     `VerifiableAIAssurance.EvidenceScope.same_identifier_can_leave_a_conflict,
     `VerifiableAIAssurance.RFC9334.health_only_is_insufficient,
     `VerifiableAIAssurance.RFC9334.policy_check_exact,
     `VerifiableAIAssurance.RFC9334.health_only_check_on_full_evidence_is_unsound,
     `VerifiableAIAssurance.RFC9334.correct_check_adds_no_new_information,
     `VerifiableAIAssurance.RFC9334.policy_check_accepts_and_rejects,
     `VerifiableAIAssurance.RFC9334.existing_ownership_information_is_enough,
     `VerifiableAIAssurance.PublicGateway.published_allow_core_respects_external_resource_policy,
     `VerifiableAIAssurance.PublicGateway.external_policy_violation_excludes_allow_core,
     `VerifiableAIAssurance.PublicGateway.published_read_example_satisfies_allow_core,
     `VerifiableAIAssurance.PublicGateway.published_read_example_satisfies_external_policy,
     `VerifiableAIAssurance.PublicGateway.published_record_preserves_selected_audit_history,
     `VerifiableAIAssurance.PublicGateway.published_record_is_sufficient_for_selected_record_questions,
     `VerifiableAIAssurance.PublicGateway.published_record_questions_preserve_history]
  for requiredName in required do
    match env.find? requiredName with
    | some (.thmInfo _) => pure ()
    | _ => Lean.throwError m!"Required theorem missing: {requiredName}"
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
