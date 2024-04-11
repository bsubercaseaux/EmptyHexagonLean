import Std
import Mathlib.Tactic.LiftLets
import Geo.SAT.ToLeanSAT.Encode

namespace LeanSAT
open Std

def PropForm.onVars (P : v → Prop) : PropForm v → Prop
  | all' as
  | any' as => ∀ a ∈ as, onVars P a
  | not' a
  | atomic' a => onVars P a
  | iff' a b => onVars P a ∧ onVars P b
  | lit _ a => P a

def Literal.eval [LitVar L v] (τ : v → Prop) (l : L) : Prop :=
  if LitVar.polarity l then τ (LitVar.toVar l) else ¬τ (LitVar.toVar l)

@[simp] theorem Literal.eval_neg [LitVar L v] [LawfulLitVar L v] (τ : v → Prop) (l : L) :
    Literal.eval τ (-l) ↔ ¬Literal.eval τ l := by
  simp [Literal.eval]; cases LitVar.polarity l <;> simp

def Clause.eval [LitVar L v] (τ : v → Prop) (cl : Clause L) : Prop :=
  ∃ l ∈ cl, Literal.eval τ l

def OptClause.eval [LitVar L v] (τ : v → Prop) : Option (Clause L) → Prop
  | none => True
  | some cl => cl.eval τ

def Cnf.eval [LitVar L v] (τ : v → Prop) (cnf : Cnf L) : Prop :=
  ∀ cl ∈ cnf, cl.eval τ

def Cnf.isUnsat [LitVar L v] (cnf : Cnf L) : Prop := ¬ ∃ τ, cnf.eval τ

theorem of_mem_toList_collectVars [LinearOrder v] (f) {acc : RBSet v compare} {P : v → Prop}
    (H : ∀ x ∈ (collectVars compare f acc).toList, P x) :
    f.onVars P ∧ (∀ x ∈ acc.toList, P x) := by
  match f with
  | .all' xs | .any' xs =>
    simp [collectVars] at H; simp [PropForm.onVars]
    have ⟨H1, H2⟩ := Array.foldl'_induction
      (fun n (acc' : RBSet v compare) =>
        (∀ x ∈ acc'.toList, P x) →
          (∀ i:Fin xs.size, i.1 < n → PropForm.onVars P xs[i]) ∧
          (∀ x ∈ RBSet.toList acc, P x)) (by simp) ?succ H
    case succ =>
      simp; intro i acc IH' H
      have ⟨IH1, IH2⟩ := of_mem_toList_collectVars _ H
      have ⟨H1, H2⟩ := IH' IH2
      refine ⟨?_, H2⟩
      simp [Nat.lt_succ_iff_lt_or_eq, or_imp, forall_and, ← Fin.ext_iff]
      exact ⟨H1, IH1⟩
    · refine ⟨fun x hx => ?_, H2⟩
      obtain ⟨n, rfl⟩ := Array.mem_iff_getElem.1 hx
      exact H1 _ n.2
  | .atomic' a | .not' a =>
    simp [collectVars] at H; simp [PropForm.onVars]
    exact of_mem_toList_collectVars a H
  | .iff' a b =>
    simp [collectVars] at H; simp [PropForm.onVars]
    have ⟨H2, H⟩ := of_mem_toList_collectVars b H
    have ⟨H1, H⟩ := of_mem_toList_collectVars a H
    exact ⟨⟨H1, H2⟩, H⟩
  | .lit b i =>
    simp [collectVars, acc.mem_toList_insert] at H; simp [PropForm.onVars]
    refine ⟨H _ (.inr rfl), fun x hx => H x <|
      or_iff_not_imp_right.2 fun xi => ⟨hx, fun eq => xi <| .symm ?_⟩⟩
    simpa [compare_eq_iff_eq] using acc.find?_some_eq_eq eq

instance : LinearOrder ILit := inferInstanceAs (LinearOrder (Subtype _))

namespace Encode

variable [LinearOrder v]
structure Context.WF (vars : Array v) : Prop where
  sorted : vars.1.Sorted (· < ·)

def PropFun (v) := (v → Prop) → Prop

def TrBase (vars : Array v) (τ : v → Prop) (σ : IVar → Prop) :=
  ∀ i : Fin vars.size, τ vars[i] ↔ σ i.1.succPNat

@[mk_iff] structure Constrained (s : State v) (σ : IVar → Prop) : Prop where
  definitions : s.definitions.find? as = some i → (σ i ↔ ∃ lit ∈ as, Literal.eval σ lit)

theorem Constrained.empty : Constrained (v := v) ⟨cl, n, ∅⟩ σ :=
  ⟨by simp [HashMap.find?_empty]⟩

def TrWF (vars : Array v) (s : State v) (f : PropFun v) :=
  (∀ τ, f τ → ∃ σ, s.clauses.eval σ ∧ Constrained s σ ∧ TrBase vars τ σ) ∧
  (∀ σ, s.clauses.eval σ → ∃ τ, f τ ∧ TrBase vars τ σ)

def Bounded (res : PropFun IVar) (max : IVar) : Prop :=
  ∀ {{σ₁ σ₂}}, (∀ i < max, σ₁ i = σ₂ i) → res σ₁ → res σ₂

theorem Bounded.mono (h : n ≤ m) (H : Bounded G n) : Bounded G m :=
  fun _ _ h1 => H fun _ h2 => h1 _ (h2.trans_le h)

theorem Bounded.iff (H : Bounded G n) {{σ₁ σ₂}} (h : ∀ i < n, σ₁ i = σ₂ i) : G σ₁ ↔ G σ₂ :=
  ⟨H h, H fun i h' => (h i h').symm⟩

theorem Bounded.apply (f : Prop → Prop) (H : Bounded G n) : Bounded (fun σ => f (G σ)) n := by
  intro σ₁ σ₂ h; simp [H.iff h]

theorem Bounded.apply₂ (f : Prop → Prop → Prop)
    (H1 : Bounded G₁ n) (H2 : Bounded G₂ n) : Bounded (fun σ => f (G₁ σ) (G₂ σ)) n := by
  intro σ₁ σ₂ h; simp [H1.iff h, H2.iff h]

theorem getElem_lt_iff {vars : Array v} (sorted : vars.1.Sorted (· < ·))
    (hi : i < vars.size) (hj : j < vars.size) : vars[i] < vars[j] ↔ i < j := by
  refine ⟨fun h => not_le.1 fun h' => ?_, List.pairwise_iff_get.1 sorted ⟨_, hi⟩ ⟨_, hj⟩⟩
  obtain h' | rfl := lt_or_eq_of_le h'
  · exact lt_asymm h <| List.pairwise_iff_get.1 sorted ⟨_, hj⟩ ⟨_, hi⟩ h'
  · exact lt_irrefl _ h

theorem getElem_inj {vars : Array v} (sorted : vars.1.Sorted (· < ·))
    (hi : i < vars.size) (hj : j < vars.size) : vars[i] = vars[j] ↔ i = j := by
  simp only [le_antisymm_iff, ← not_lt]; simp [getElem_lt_iff sorted, hi, hj]

theorem binSearch_wf (sorted : vars.1.Sorted (· < ·)) (h : i < vars.size) :
    binSearch (v := v) compare vars vars[i] = i := by
  let rec go (lo hi : Nat) (hlo : lo ≤ i) (hhi : i ≤ hi) (hhi' : hi < vars.size) :
      binSearch.go compare vars vars[i] lo hi = i := by
    have mhi : lo ≤ hi := hlo.trans hhi
    unfold binSearch.go; rw [if_pos (hlo.trans hhi)]; lift_lets; intro x m a
    have mhi : (lo + hi) / 2 ≤ hi := by omega
    have mhi' : m < vars.size := mhi.trans_lt hhi'
    simp [a, Array.getElem?_eq_getElem _ _ mhi']
    split <;> rename_i eq <;> simp [compare_eq_iff_eq, compare_lt_iff_lt, compare_gt_iff_gt] at eq
    · rw [getElem_lt_iff sorted] at eq
      exact go (m + 1) hi eq hhi hhi'
    · rw [getElem_lt_iff sorted] at eq
      have := Nat.not_eq_zero_of_lt eq
      rw [if_neg this]
      exact go lo (m - 1) hlo (Nat.le_pred_of_lt eq) ((Nat.pred_le _).trans_lt mhi')
    · rwa [getElem_inj sorted] at eq
  termination_by hi + 1 - lo
  decreasing_by all_goals decreasing_with omega
  exact go 0 (vars.size - 1) (Nat.zero_le _) (Nat.le_pred_of_lt h) (Nat.pred_lt' h)

def WFCtx (v) [LinearOrder v] := {vars : Array v // vars.1.Sorted (· < ·)}

structure WFState (c : WFCtx v) where
  s : State v
  f : PropFun v
  lt : c.1.size < s.nextVar
  to_σ : f τ → ∃ σ, s.clauses.eval σ ∧ TrBase c.1 τ σ
  to_τ : s.clauses.eval σ → ∃ τ, f τ ∧ TrBase c.1 τ σ
  bounded : Bounded s.clauses.eval s.nextVar
  definitions : s.definitions.find? as = some i →
    i < s.nextVar ∧ ∀ σ, s.clauses.eval σ → (σ i ↔ ∃ lit ∈ as, Literal.eval σ lit)

structure WFState.LE (s s' : WFState (v := v) c) : Prop where
  f : s'.f τ → s.f τ
  nextVar : s.s.nextVar ≤ s'.s.nextVar
  clauses : Cnf.eval σ s'.s.clauses → Cnf.eval σ s.s.clauses

instance : LE (WFState (v := v) c) := ⟨WFState.LE⟩

theorem WFState.LE.rfl {s : WFState (v := v) c} : s ≤ s := ⟨id, le_rfl, id⟩

theorem WFState.LE.trans {s₁ s₂ s₃ : WFState (v := v) c} : s₁ ≤ s₂ → s₂ ≤ s₃ → s₁ ≤ s₃ :=
  fun ⟨f₁, n₁, c₁⟩ ⟨f₂, n₂, c₂⟩ => ⟨f₁ ∘ f₂, le_trans n₁ n₂, c₁ ∘ c₂⟩

def WFState.init : WFState (v := v) c := by
  refine ⟨⟨#[], c.1.size.succPNat, ∅⟩, fun _ => True, Nat.lt_succ_self _,
      fun {τ} => ?_, fun {σ} _ => ?_, fun _ _ => ?_, ?_⟩ <;>
    simp [Cnf.eval, HashMap.find?_empty, TrBase]
  · exact ⟨fun i => ∃ h : _, τ (c.1[i.natPred]'h), by simp⟩
  · exact ⟨fun i => σ (binSearch compare c.1 i).succPNat, fun i => by simp [binSearch_wf c.2]⟩

def M.evalsTo (c) (x : M v α) (s s' : WFState (v := v) c) (a : α) :=
  (x.run c.1).run s.s = (a, s'.s) ∧ s ≤ s'

theorem M.evalsTo.pure : (pure a : M v α).evalsTo c s s a := ⟨rfl, .rfl⟩

theorem M.evalsTo.bind {x : M v α} {g : α → M v β}
    (h₁ : x.evalsTo c s₁ s₂ a) (h₂ : (g a).evalsTo c s₂ s₃ b) : (x >>= g).evalsTo c s₁ s₃ b := by
  simp [evalsTo] at *; simp [h₁, h₂, WFState.LE.trans h₁.2 h₂.2]

theorem forM'.evalsTo (as : Array α) (f : (a : α) → a ∈ as → M v Unit)
    (motive : WFState c → Nat → Prop)
    (zero : motive s 0)
    (succ : ∀ {s} (i : Fin as.size), motive s i →
      ∃ s', (f as[i] (Array.getElem?_mem ..)).evalsTo c s s' () ∧ motive s' (i+1))
    : ∃ s', (as.forM' f).evalsTo c s s' () ∧ motive s' as.size := by
  let rec go (i) (hi : i ≤ as.size) {s : WFState c} (hs : motive s i) :
      ∃ s', (Array.foldlM'.go as (fun _ => f) i ()).evalsTo c s s' () ∧ motive s' as.size := by
    unfold Array.foldlM'.go; split
    · let ⟨s₁, h₁, hs⟩ := succ ⟨i, ‹_›⟩ hs
      let ⟨s', h₂, hs⟩ := go (i+1) ‹_› hs
      exact ⟨s', M.evalsTo.bind h₁ h₂, hs⟩
    · cases le_antisymm hi (not_lt.1 ‹_›)
      exact ⟨_, .pure, hs⟩
  termination_by as.size - i
  exact go 0 (Nat.zero_le _) zero

def WFState.Evaluates (s : WFState (v := v) c) (F : PropFun v) (G : PropFun IVar) : Prop :=
  Bounded G s.s.nextVar ∧
  ∀ τ, s.f τ → ∀ σ, s.s.clauses.eval σ ∧ TrBase c.1 τ σ → (F τ ↔ G σ)

theorem WFState.Evaluates.mono {s s' : WFState (v := v) c} (h : s ≤ s') :
    s.Evaluates F G → s'.Evaluates F G := by
  refine fun ⟨H1, H2⟩ => ⟨fun σ₁ σ₂ h1 => ?_, fun τ h1 σ ⟨h2, h3⟩ => ?_⟩
  · exact H1 fun i hl => h1 i (hl.trans_le h.nextVar)
  · exact H2 τ (h.f h1) σ ⟨h.clauses h2, h3⟩

theorem WFState.Evaluates.apply₂ {s : WFState (v := v) c} (f : Prop → Prop → Prop) :
    s.Evaluates F₁ G₁ → s.Evaluates F₂ G₂ →
    s.Evaluates (fun τ => f (F₁ τ) (F₂ τ)) (fun σ => f (G₁ σ) (G₂ σ))
  | ⟨B1, H1⟩, ⟨B2, H2⟩ =>
    ⟨B1.apply₂ f B2, fun τ hτ σ hσ => by simp [H1 τ hτ σ hσ, H2 τ hτ σ hσ]⟩

theorem WFState.Evaluates.apply {s : WFState (v := v) c} (f : Prop → Prop)
    (H : s.Evaluates F G) : s.Evaluates (fun τ => f (F τ)) (fun σ => f (G σ)) :=
  H.apply₂ (fun _ => f) H

theorem WFState.Evaluates.const {s : WFState (v := v) c} (p : Prop) :
    s.Evaluates (fun _ => p) (fun _ => p) :=
  ⟨fun _ _ _ => id, fun _ _ _ _ => .rfl⟩

-- theorem WFState.Evaluates.const_iff {s : WFState (v := v) c} {p : Prop} :
--     s.Evaluates F (fun _ => p) ↔ F = fun _ => p := by
--   refine ⟨fun H => ?_, fun H => H ▸ .const _⟩; funext τ; ext
--   have := H.2 τ


theorem fin_lt_nextVar {s : WFState (v := v) c} (i : Fin c.1.size) : i.1.succPNat < s.s.nextVar :=
  (Nat.succ_le_succ i.2).trans s.lt

theorem WFState.Evaluates.var {s : WFState (v := v) c} (h : i < c.1.size) :
    s.Evaluates (fun τ => τ c.1[i]) (fun σ => σ i.succPNat) :=
  ⟨fun _ _ h1 => cast (h1 _ <| fin_lt_nextVar ⟨_, h⟩), fun _ _ _ ⟨_, hτσ⟩ => hτσ ⟨_, h⟩⟩

theorem WFState.Evaluates.defn {s : WFState (v := v) c} (h : s.s.definitions.find? as = some i)
    (H : s.Evaluates F (∃ lit ∈ as, Literal.eval · lit)) : s.Evaluates F (· i) :=
  have ⟨hd1, hd2⟩ := s.definitions h
  ⟨fun _ _ h1 => cast (h1 _ hd1), fun τ hτ σ hσ => (H.2 τ hτ σ hσ).trans (hd2 σ hσ.1).symm⟩

theorem encodeLit.wf (pos) {i} (hf : i ∈ c.1) (s) :
    ∃ l, M.evalsTo (v := v) c (encodeLit compare pos i) s s l ∧
      s.Evaluates (fun τ ↦ τ i ↔ pos) (Literal.eval · l) := by
  obtain ⟨k, rfl⟩ := Array.mem_iff_getElem.1 hf
  refine ⟨_, ⟨rfl, .rfl⟩, ?_⟩; simp [binSearch_wf c.2]
  convert (WFState.Evaluates.var k.2).apply (· ↔ pos)
  simp [Literal.eval]; cases pos <;> simp

theorem getAny.wf (as : Array ILit) (s F)
    (hcl : s.Evaluates (v := v) F (∃ l ∈ as, Literal.eval · l)) :
    ∃ s' i, M.evalsTo (v := v) c (getAny as) s s' i ∧
    s'.f = s.f ∧ s'.Evaluates F (· i) := by
  unfold getAny; lift_lets; intro as' jp
  replace hcl : s.Evaluates (v := v) F (∃ l ∈ as', Literal.eval · l) := by
    simpa [as', Array.mem_sortAndDeduplicate] using hcl
  clear_value as'; clear as
  change ∃ s' i, M.evalsTo c
    (match HashMap.find? s.s.definitions as' with
    | some i => pure i
    | _ => jp ()) s s' i ∧ _
  split
  · exact ⟨_, _, .pure, rfl, .defn ‹_› hcl⟩
  · let new := s.s.nextVar
    have heval {σ} :
        Cnf.eval σ
          (as'.foldl (fun clauses a => clauses.push #[-a, LitVar.mkPos new]) s.s.clauses
            |>.push (as'.push (-LitVar.mkPos new)))
          ↔ Cnf.eval σ s.s.clauses ∧ ((∃ l ∈ as', Literal.eval σ l) ↔ σ new) := by
      rw [@iff_def _ (σ new)]; simp [Cnf.eval, or_imp, forall_and, ← and_assoc]
      apply and_congr
      · refine (Array.foldl_induction
          (motive := fun n (cnf : ICnf) => (∀ x ∈ cnf, Clause.eval σ x) ↔
            (∀ cl ∈ s.s.clauses, Clause.eval σ cl) ∧
            ∀ i : Fin as'.size, i < n → Literal.eval σ as'[i] → σ new)
          (by simp) (fun i cnf IH => ?_)).trans (by simp [Array.mem_iff_getElem])
        simp [IH, or_imp, forall_and, Nat.lt_succ_iff_lt_or_eq, ← Fin.ext_iff, and_assoc]
        rintro - -; simp [Clause.eval, ← imp_iff_not_or]; apply imp_congr_right
        rintro -; rw [Literal.eval, LawfulLitVar.toVar_mkPos]; simp
      · simp [Clause.eval, or_and_right, exists_or, ← imp_iff_or_not]; rw [Literal.eval]; simp
    refine
      ⟨{ s := _, f := _, lt := ?lt
         to_σ := ?to_σ, to_τ := ?to_τ, bounded := ?bd, definitions := ?df },
       _, ⟨rfl, ?le⟩, rfl, ?ev⟩ <;> dsimp
    case lt => exact Nat.lt_succ_of_lt s.lt
    case to_σ =>
      intro τ hτ
      have ⟨σ, hσ, hστ⟩ := s.to_σ hτ
      let σ' := Function.update σ new (∃ l ∈ as', Literal.eval σ l)
      have eqσ (i) (hi : i < s.s.nextVar) : σ' i = σ i := Function.update_noteq (ne_of_lt hi) ..
      have hσ' := (s.bounded.iff eqσ).2 hσ
      refine ⟨σ', ?_, fun i => ?_⟩
      · exact heval.2 ⟨hσ', by simpa only [σ', Function.update_same] using hcl.1.iff eqσ⟩
      · exact (hστ i).trans <| .symm <| .of_eq <|
          Function.update_noteq (ne_of_lt <| fin_lt_nextVar i) ..
    case to_τ => intro σ hσ; exact s.to_τ (heval.1 hσ).1
    case bd =>
      simp [heval]
      have H := Nat.le_succ new
      exact (s.bounded.mono H).apply₂ And <| (hcl.1.mono H).apply₂ Iff
        fun σ₁ σ₂ eq => cast (eq _ (Nat.lt_succ_self _))
    case df =>
      simp [heval]; intro as i eq
      obtain eq | ⟨rfl, rfl⟩ := HashMap.of_find?_insert eq
      · have ⟨h1, h2⟩ := s.definitions eq
        exact ⟨Nat.lt_succ_of_lt h1, fun σ h _ => h2 σ h⟩
      · exact ⟨Nat.lt_succ_self _, fun _ _ => Iff.symm⟩
    case le => exact ⟨id, Nat.le_succ _, by simp (config := { contextual := true }) [heval]⟩
    case ev =>
      refine ⟨fun σ₁ σ₂ eq => cast (eq _ (Nat.lt_succ_self _)), ?_⟩
      simp [heval]; intro τ hτ σ hσ₁ hσ₂ hστ
      exact (hcl.2 _ hτ _ ⟨hσ₁, hστ⟩).trans hσ₂

theorem toLit.any_wf (c) (G : α → PropFun v)
    (as : Array α) (f : (a : α) → a ∈ as → M v ILit) (pos)
    (IH : ∀ a h, ∀ s, ∃ s' l, (f a h).evalsTo c s s' l ∧ s'.f = s.f ∧
      s'.Evaluates (G a) (Literal.eval · l))
    (s) : ∃ s' l,
      (return LitVar.mkLit ILit (← getAny (← as.mapM'' f)) pos).evalsTo c s s' l ∧ s'.f = s.f ∧
      s'.Evaluates (fun τ => (∃ a ∈ as, G a τ) ↔ pos) (Literal.eval · l) := by
  let rec go (i) (s : WFState c) (ls : Array ILit)
      (hl : s.Evaluates (∃ j:Fin as.size, j.1 < i ∧ G as[j] ·) (∃ l ∈ ls, Literal.eval · l)) :
      ∃ s' ls', (Array.foldlM'.go as (·.push <$> f · ·) i ls).evalsTo c s s' ls' ∧ s'.f = s.f ∧
        s'.Evaluates (∃ a ∈ as, G a ·) (∃ l ∈ ls', Literal.eval · l) := by
    unfold Array.foldlM'.go; split
    · obtain ⟨i, rfl⟩ : ∃ i':Fin _, i'.1 = i := ⟨⟨i, ‹_›⟩, rfl⟩
      rw [← bind_pure_comp]; simp
      let ⟨s1, l, et1, f1, ev1⟩ := IH as[i] (as.getElem?_mem (i := i)) s
      let ⟨s2, ls', et2, f2, ev2⟩ := go (i+1) ‹_› (ls.push l) <| by
        convert (hl.mono et1.2).apply₂ Or ev1 <;>
          simp [Nat.lt_succ, le_iff_lt_or_eq, or_and_right, exists_or, ← Fin.ext_iff]
      exact ⟨s2, ls', et1.bind et2, f2.trans f1, ev2⟩
    · refine ⟨s, ls, .pure, rfl, ?_⟩; convert hl
      simp [Array.mem_iff_getElem, fun j : Fin as.size => j.2.trans_le (not_lt.1 ‹_›)]
  termination_by as.size - i
  let ⟨s1, ls, et1, f1, ev1⟩ := go 0 s #[] (by simp [WFState.Evaluates, Bounded])
  let ⟨s2, i, et2, f2, ev2⟩ := getAny.wf ls s1 _ ev1
  refine ⟨s2, _, et1.bind <| et2.bind <| .pure, f2.trans f1, ?_⟩
  convert ev2.apply (· ↔ pos); simp [Literal.eval]; cases pos <;> simp

theorem toLit.wf (f : PropForm v) (pos) (hf : f.onVars (· ∈ c.1)) (s) :
    ∃ s' l, (toLit compare f pos).evalsTo c s s' l ∧ s'.f = s.f ∧
      s'.Evaluates (fun τ => f.eval τ ↔ pos) (Literal.eval · l) := by
  unfold toLit; split <;> try simp [PropForm.onVars] at hf ⊢
  next /-neg'-/ a =>
    convert toLit.wf a (!pos) hf s using 8
    cases pos <;> simp [PropForm.eval]
  next /-atomic'-/ a => exact toLit.wf a pos hf s
  next /-lit'-/ pos' i =>
    use s; simp; convert encodeLit.wf _ hf s using 5
    cases pos <;> simp; cases pos' <;> simp
  next /-all'-/ as =>
    convert toLit.any_wf c _ as _ (!pos) (fun a h => toLit.wf a false (hf a h)) s using 8
    cases pos <;> simp
  next /-any'-/ as =>
    exact toLit.any_wf c _ as _ pos (fun a h => by simpa using toLit.wf a true (hf a h)) s
  next /-iff'-/ a b =>
    let ⟨s1, a', et1, f1, ev1⟩ := toLit.wf a true hf.1 s
    let ⟨s2, b', et2, f2, ev2⟩ := toLit.wf b true hf.2 s1
    replace ev1 := ev1.mono et2.2
    let ⟨s3, ab, et3, f3, ev3⟩ := getAny.wf #[-a', b'] s2 (fun τ => a.eval τ → b.eval τ) <| by
      convert ev1.apply₂ (·→·) ev2 using 2 <;> simp [Clause.eval, ← imp_iff_not_or]
    replace ev1 := ev1.mono et3.2; replace ev2 := ev2.mono et3.2
    let ⟨s4, ba, et4, f4, ev4⟩ := getAny.wf #[a', -b'] s3 (fun τ => b.eval τ → a.eval τ) <| by
      convert ev1.apply₂ (fun a b => b → a) ev2 using 2 <;> simp [Clause.eval, ← imp_iff_or_not]
    replace ev3 := ev3.mono et4.2
    let ⟨s5, v, et5, f5, ev5⟩ := getAny.wf #[-LitVar.mkPos ab, -LitVar.mkPos ba] s4
      (fun τ => ¬(a.eval τ ↔ b.eval τ))
      (by convert ev3.apply₂ (fun a b => ¬(a ∧ b)) ev4 using 2 <;>
            simp [Clause.eval, Literal.eval, ← imp_iff_not_or]; tauto)
    refine ⟨s5, _, et1.bind <| et2.bind <| et3.bind <| et4.bind <| et5.bind .pure, ?_, ?_⟩
    · rw [f5, f4, f3, f2, f1]
    · convert ev5.apply (· ↔ !pos) using 2 <;> cases pos <;> simp [Literal.eval]
termination_by f
decreasing_by all_goals decreasing_with subst_vars; first | decreasing_trivial

theorem pushClause.wf (cl s F) (hcl : s.Evaluates (v := v) F (Clause.eval · cl)) :
    ∃ s', (pushClause cl).evalsTo c s s' () ∧ ∀ τ, s'.f τ ↔ s.f τ ∧ F τ :=
  ⟨{s with
      f := fun τ => s.f τ ∧ F τ
      s.clauses := s.s.clauses.push cl
      bounded := fun _ _ h1 h2 => by
        have := s.bounded h1
        simp [Cnf.eval, or_imp, forall_and] at this h2 ⊢
        exact ⟨this h2.1, hcl.1 h1 h2.2⟩
      to_τ := fun {σ} hσ => by
        simp [Cnf.eval, or_imp, forall_and] at hσ
        let ⟨τ, hτ, hτσ⟩ := s.to_τ (σ := σ) hσ.1
        refine ⟨τ, ⟨hτ, ?_⟩, hτσ⟩
        simpa [Cnf.eval, eq_true hσ.1, hτσ, hσ] using hcl.2 τ hτ σ
      to_σ := fun {τ} ⟨hτ, fτ⟩ => (s.to_σ hτ).imp fun σ ⟨hσ, hτσ⟩ => by
        simp [Cnf.eval] at hσ
        simpa [Cnf.eval, or_imp, forall_and, eq_true hσ, hτσ, fτ] using hcl.2 τ hτ σ
      definitions := fun {as i} h => by
        let ⟨hd1, hd2⟩ := s.definitions h
        refine ⟨hd1, fun σ hσ => hd2 σ ?_⟩
        simp [Cnf.eval, or_imp, forall_and] at hσ ⊢; exact hσ.1
    },
    ⟨rfl, by constructor <;> simp (config := {contextual := true}) [Cnf.eval]⟩,
    by simp⟩

theorem pushFmla.foldlM'_wf (as : Array (α))
    (FF : Option IClause → (a : α) → a ∈ as → M v (Option IClause))
    (G : α → PropFun v)
    (IH : ∀ a h s F ocl, s.Evaluates F (OptClause.eval · ocl) →
      ∃ s' ocl', (FF ocl a h).evalsTo c s s' ocl' ∧
        s'.f = s.f ∧ s'.Evaluates (fun τ => F τ ∨ G a τ) (OptClause.eval · ocl'))
    (s) (ev : s.Evaluates F (OptClause.eval · ocl)) :
    ∃ s' ocl', (as.foldlM' FF ocl).evalsTo c s s' ocl' ∧
      s'.f = s.f ∧ s'.Evaluates (fun τ => F τ ∨ ∃ a ∈ as, G a τ) (OptClause.eval · ocl') :=
  let rec go (i) (s) {ocl}
    (ev : by
      exact s.Evaluates
        (fun τ => F τ ∨ ∃ j:Fin as.size, j < i ∧ G as[j] τ) (OptClause.eval · ocl)) :
    ∃ s' ocl', (Array.foldlM'.go as FF i ocl).evalsTo c s s' ocl' ∧
      s'.f = s.f ∧ s'.Evaluates (fun τ => F τ ∨ ∃ a ∈ as, G a τ) (OptClause.eval · ocl') := by
    unfold Array.foldlM'.go; split
    · obtain ⟨i, rfl⟩ : ∃ i':Fin _, i'.1 = i := ⟨⟨i, ‹_›⟩, rfl⟩
      have := IH as[i] (Array.getElem?_mem ..) s _ ocl ev
      let ⟨s1, ocl1, et1, f1, ev1⟩ := IH as[i] (Array.getElem?_mem ..) s _ ocl ev
      let ⟨s2, ocl2, et2, f2, ev2⟩ := go (i+1) s1 (ocl := ocl1) <| by
        convert ev1 using 2
        simp [or_assoc, Nat.lt_succ_iff_lt_or_eq, or_and_right, exists_or, ← Fin.ext_iff]
      exact ⟨s2, ocl2, et1.bind et2, f2.trans f1, ev2⟩
    · refine ⟨_, _, .pure, rfl, ?_⟩
      simpa [Array.mem_iff_getElem, fun j : Fin as.size => j.2.trans_le (not_lt.1 ‹_›)] using ev
  termination_by as.size - i
  go 0 s <| by simpa using ev

-- Only needed because of lean4#3843
theorem pushFmla.induction {cmp}
    (motive : PropForm v → Bool → Option IClause → M v (Option IClause) → Prop)
    (h1 : ∀ f b, motive f b none (pure none))
    (h2 : ∀ cl, motive .true true cl (pure none))
    (h3 : ∀ cl, motive .false false cl (pure none))
    (h4 : ∀ as cl IH, (∀ cl a h, motive a false cl (IH cl a h)) →
      motive (.all' as) false cl (as.foldlM' (init := cl) IH))
    (h5 : ∀ as cl IH, (∀ cl a h, motive a true cl (IH cl a h)) →
      motive (.any' as) true cl (as.foldlM' (init := cl) IH))
    (h6 : ∀ f b cl IH, motive f (!b) cl IH → motive (.not' f) b cl IH)
    (h7 : ∀ f b cl, motive f b (some cl) (return some <| cl.push <| ← toLit cmp f b))
    (f b cl) : motive f b cl (pushFmla cmp f b cl) := by
  have p := show let α := _; let R := _; @WellFounded α R from @_unary.proof_1 v
  revert p; lift_lets; intro α R wf
  delta pushFmla _unary
  conv => arg 4; tactic => exact show _ = @WellFounded.fix α _ R wf (let wfF := _; wfF) _ from rfl
  lift_lets; intro wfF
  suffices ∀ fix : α → _, (∀ x, fix x = wfF x (fun y _ => fix y)) →
      motive f b cl (fix ⟨f, b, cl⟩) by
    exact this _ (fun _ => WellFounded.fix_eq ..)
  revert wfF; dsimp; intro fix wfF_eq
  refine wf.induction (C := fun x => motive x.1 x.2.1 x.2.2 (fix x))
    ⟨f, b, cl⟩ fun ⟨f, b, cl⟩ IH => ?_
  replace IH {f b cl} (hr := by decreasing_tactic) := IH ⟨f, b, cl⟩ hr
  dsimp; rw [wfF_eq]; clear wfF_eq
  unfold match_1; dsimp; cases f <;> dsimp
  case all' =>
    split
    · rename Array.size _ = 0 => h; have := Array.eq_empty_of_size_eq_zero h
      subst this; simp; clear h
      cases b <;> (cases cl <;> dsimp <;> [apply h1; skip])
      · apply h4; simp
      · apply h2
    · cases b <;> (cases cl <;> dsimp <;> [apply h1; skip])
      · apply h4; intro cl a h; exact IH
      · apply h7
  case any' =>
    split
    · rename Array.size _ = 0 => h; have := Array.eq_empty_of_size_eq_zero h
      subst this; simp; clear h
      cases b <;> (cases cl <;> dsimp <;> [apply h1; skip])
      · apply h3
      · apply h5; simp
    · cases b <;> (cases cl <;> dsimp <;> [apply h1; skip])
      · apply h7
      · apply h5; intro cl a h; exact IH
  case not' =>
    cases cl <;> dsimp <;> [apply h1; skip]
    apply h6; exact IH
  all_goals
    cases cl <;> dsimp <;> [apply h1; skip]
    apply h7

theorem pushFmla.wf (f : PropForm v) (pos) (hf : f.onVars (· ∈ c.1)) (ocl F s)
    (ev : s.Evaluates F (OptClause.eval · ocl)) :
    ∃ s' ocl', (pushFmla compare f pos ocl).evalsTo c s s' ocl' ∧
      s'.f = s.f ∧ s'.Evaluates (fun τ => F τ ∨ (f.eval τ ↔ pos)) (OptClause.eval · ocl') := by
  revert hf F s ev
  have H1 (G : PropFun _) (F s) (ev : s.Evaluates F (fun _ => True)) : ∃ s' ocl',
    M.evalsTo c (pure none) s s' (ocl' : Option IClause) ∧
      s'.f = s.f ∧ s'.Evaluates (fun τ ↦ F τ ∨ G τ) (OptClause.eval · ocl') :=
    ⟨s, none, .pure, rfl, ev.1, fun τ hτ σ hσ =>
      iff_true_intro <| Or.inl <| (ev.2 τ hτ σ hσ).2 trivial⟩
  apply pushFmla.induction (motive := fun f pos ocl x =>
    f.onVars (· ∈ c.1) → ∀ F s, s.Evaluates F (OptClause.eval · ocl) →
    ∃ s' ocl', x.evalsTo c s s' ocl' ∧
      s'.f = s.f ∧ s'.Evaluates (fun τ => F τ ∨ (f.eval τ ↔ pos)) (OptClause.eval · ocl'))
  · exact fun _ _ _ => H1 _
  iterate 2
    · intros; exact ⟨_, none, .pure, rfl, by simpa [OptClause.eval] using .const True⟩
  iterate 2
    · intro as cl FF IH hf F s ev; simp [PropForm.onVars] at hf ⊢
      refine pushFmla.foldlM'_wf as FF _ ?_ s ev
      intro a h s F ocl; simpa using IH _ _ _ (hf a h) F s
  · intro f b cl x IH hf F s ev
    convert IH (by simpa [PropForm.onVars] using hf) F s ev using 5; cases b <;> simp
  · intro f b cl hf F s ev
    let ⟨s1, l, et1, f1, ev1⟩ := toLit.wf f b hf s
    refine ⟨s1, _, et1.bind .pure, f1, ?_⟩
    convert (ev.mono et1.2).apply₂ Or ev1
    simp [OptClause.eval, Clause.eval, or_and_right, exists_or]

theorem toICnfAny.wf (as : Array (PropForm v)) (pos) (has : ∀ a ∈ as, a.onVars (· ∈ c.1)) (s) :
    ∃ s', (toICnfAny compare as pos).evalsTo c s s' () ∧
      ∀ τ, s'.f τ ↔ s.f τ ∧ (∃ a ∈ as, a.eval τ ↔ pos) := by
  unfold toICnfAny
  let ⟨s1, ocl1, et1, f1, ev1⟩ := pushFmla.foldlM'_wf as (fun cl f _ => pushFmla compare f pos cl)
    (·.eval · ↔ pos)
    (fun a h _ _ _ => pushFmla.wf a pos (has _ h) _ _ _)
    s (F := fun _ => False) (ocl := some #[])
    (by simpa [OptClause.eval, Clause.eval] using .const False)
  simp at ev1
  have ⟨s2, et2, f2⟩ : ∃ s2,
    M.evalsTo c (match ocl1 with | some cl => pushClause cl | x => pure ())
      s1 s2 () ∧ ∀ τ, s2.f τ ↔ s1.f τ ∧ ∃ a ∈ as, a.eval τ ↔ pos := by
    cases ocl1 <;> simp [OptClause.eval] at ev1 ⊢
    · refine ⟨_, .pure, fun τ => (and_iff_left_of_imp fun hτ => ?_).symm⟩
      have ⟨σ, hσ⟩ := s1.to_σ hτ
      exact (ev1.2 τ hτ σ hσ).2 trivial
    · exact pushClause.wf _ _ _ ev1
  exact ⟨s2, et1.bind et2, f1 ▸ f2⟩

theorem pushICnf.all_wf (c) (G : α → PropFun v)
    (as : Array α) (f : (a : α) → a ∈ as → M v Unit)
    (IH : ∀ a h, ∀ s, ∃ s', (f a h).evalsTo c s s' () ∧ ∀ τ, s'.f τ ↔ s.f τ ∧ G a τ)
    (s) : ∃ s', (as.forM' f).evalsTo c s s' () ∧ ∀ τ, s'.f τ ↔ s.f τ ∧ ∀ a ∈ as, G a τ := by
  refine
    let ⟨s', h, hs⟩ := forM'.evalsTo as f (s := s)
      (motive := fun s' n => ∀ τ, s'.f τ ↔ s.f τ ∧ ∀ i:Fin as.size, i < n → G as[i] τ)
      (by simp) ?_; ⟨s', h, fun τ => ?_⟩
  · intro s₁ i H
    let ⟨s', h, hs⟩ := IH as[i] (Array.getElem?_mem ..) s₁
    refine ⟨s', h, fun τ => ?_⟩
    simp [hs, H, and_assoc, Nat.lt_succ_iff, le_iff_lt_or_eq, or_imp, forall_and, ← Fin.ext_iff]
  · simp [hs, Array.mem_iff_getElem]

theorem pushICnf.wf (f : PropForm v) (pos) (hf : f.onVars (· ∈ c.1)) (s) :
    ∃ s', (pushICnf compare f pos).evalsTo c s s' () ∧ ∀ τ, s'.f τ ↔ s.f τ ∧ (f.eval τ ↔ pos) := by
  unfold pushICnf; split <;> try simp [PropForm.onVars] at hf ⊢
  next /-neg'-/ a =>
    let ⟨s', h1, h2⟩ := pushICnf.wf a (!pos) hf s
    exact ⟨s', h1, by simp [h2]; cases pos <;> simp [PropForm.eval]⟩
  next /-all'-/ as =>
    exact pushICnf.all_wf c _ as _ (fun a h => by simpa using pushICnf.wf a true (hf a h)) s
  next /-¬any'-/ as =>
    exact pushICnf.all_wf c _ as _ (fun a h => by simpa using pushICnf.wf a false (hf a h)) s
  next /-¬all'-/ as => simpa using toICnfAny.wf as false hf s
  next /-any'-/ as => simpa using toICnfAny.wf as true hf s
  next /-iff'-/ a b =>
    let ⟨s1, a', et1, f1, ev1⟩ := toLit.wf a true hf.1 s
    let ⟨s2, b', et2, f2, ev2⟩ := toLit.wf b pos hf.2 s1
    replace ev1 := ev1.mono et2.2
    let ⟨s3, et3, f3⟩ := pushClause.wf #[-a', b'] s2 (fun τ => a.eval τ → (b.eval τ ↔ pos)) <| by
      convert ev1.apply₂ (·→·) ev2 using 2 <;> simp [Clause.eval, ← imp_iff_not_or]
    replace ev1 := ev1.mono et3.2; replace ev2 := ev2.mono et3.2
    let ⟨s4, et4, f4⟩ := pushClause.wf #[a', -b'] s3 (fun τ => (b.eval τ ↔ pos) → a.eval τ) <| by
      convert ev1.apply₂ (fun a b => b → a) ev2 using 2 <;> simp [Clause.eval, ← imp_iff_or_not]
    refine ⟨s4, et1.bind <| et2.bind <| et3.bind et4, fun τ => ?_⟩
    simp [f4, f3, f2, f1, and_assoc, ← iff_def]; tauto
  next /-other-/ => simpa using toICnfAny.wf #[f] pos (by simpa using hf) s
decreasing_by all_goals decreasing_with subst_vars; decreasing_trivial

end Encode
open Encode

theorem PropForm.toICnf_sat [LinearOrder v] (f : PropForm v) :
    (∃ σ, Cnf.eval σ (f.toICnf compare).2) ↔ ∃ τ, eval τ f := by
  unfold toICnf; lift_lets; intro vars
  have allMem : f.onVars (· ∈ vars) := by
    refine (of_mem_toList_collectVars f (acc := ∅) fun x hx => ?_).1
    simpa [vars, Std.RBSet.toArray_eq, Array.mem_def] using hx
  have sorted : vars.1.Sorted (· < ·) := by
    simp [vars, Std.RBSet.toArray_eq]
    exact RBSet.toList_sorted.imp (by simp [RBNode.cmpLT_iff, compare_lt_iff_lt])
  clear_value vars; split; rename_i s _ clauses var next eq
  obtain ⟨⟨s', F, _, wf₁, wf₂, _⟩, ⟨eq', -⟩, val⟩ :=
    pushICnf.wf (c := ⟨_, sorted⟩) f true allMem .init
  cases eq.symm.trans eq'; simp [WFState.init] at val; simp [← val]
  refine ⟨fun ⟨σ, hσ⟩ => ?_, fun ⟨τ, hτ⟩ => ?_⟩
  · let ⟨τ, hτ⟩ := wf₂ hσ; exact ⟨τ, by simpa using hτ.1⟩
  · let ⟨σ, hσ, _⟩ := wf₁ (τ := τ) (by simpa using hτ); exact ⟨σ, hσ⟩
