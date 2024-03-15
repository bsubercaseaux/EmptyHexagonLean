import Geo.Definitions.Structures
import Geo.Definitions.SigmaEquiv

namespace Geo
open Classical List

def σIsEmptyTriangleFor (a b c : Point) (S : Set Point) : Prop :=
  ∀ s ∈ S, ¬σPtInTriangle s a b c

theorem σIsEmptyTriangleFor.perm₁ : σIsEmptyTriangleFor p q r S → σIsEmptyTriangleFor q p r S :=
  fun H s hs hn => H s hs hn.perm₁

theorem σIsEmptyTriangleFor.perm₂ : σIsEmptyTriangleFor p q r S → σIsEmptyTriangleFor p r q S :=
  fun H s hs hn => H s hs hn.perm₂

theorem σIsEmptyTriangleFor.perm (h : [p, q, r].Perm [p', q', r']) :
    σIsEmptyTriangleFor p q r S ↔ σIsEmptyTriangleFor p' q' r' S :=
  perm₃_induction (P := (σIsEmptyTriangleFor · · · S))
    (fun _ _ _ => (·.perm₁)) (fun _ _ _ => (·.perm₂)) h

def σHasEmptyKGon (n : Nat) (S : Set Point) : Prop :=
  ∃ s : Finset Point, s.card = n ∧ ↑s ⊆ S ∧
    ∀ᵉ (a ∈ s) (b ∈ s) (c ∈ s), a ≠ b → a ≠ c → b ≠ c →
      σIsEmptyTriangleFor a b c S

theorem σIsEmptyTriangleFor_iff_diff (gp : Point.InGenPos₃ a b c) :
    σIsEmptyTriangleFor a b c S ↔ σIsEmptyTriangleFor a b c (S\{a,b,c}) := by
  refine ⟨fun H x h => H x h.1, fun H x h hn => H x ⟨h, ?_⟩ hn⟩
  rintro (rfl|rfl|rfl)
  · exact not_mem_σPtInTriangle gp.perm₁ hn.perm₁
  · exact not_mem_σPtInTriangle gp hn
  · exact not_mem_σPtInTriangle gp.perm₂ hn.perm₂

theorem σIsEmptyTriangleFor_iff (gp : Point.ListInGenPos S)
  (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (ab : a ≠ b) (ac : a ≠ c) (bc : b ≠ c) :
  σIsEmptyTriangleFor a b c S.toFinset ↔ EmptyShapeIn {a, b, c} S.toFinset := by
  rw [σIsEmptyTriangleFor_iff_diff]
  · simp [not_or, σIsEmptyTriangleFor, EmptyShapeIn]
    repeat refine forall_congr' fun _ => ?_
    rw [σPtInTriangle_iff, PtInTriangle]; apply gp.subperm₄
    simp [*, List.subperm_of_subset]
  · apply Point.ListInGenPos.subperm.1 gp
    simp [*, List.subperm_of_subset]

theorem σIsEmptyTriangleFor_iff' {a b c : Point} (gp : Point.ListInGenPos S)
    (hs : [a, b, c] <+~ S) :
    EmptyShapeIn [a, b, c].toFinset S.toFinset ↔ σIsEmptyTriangleFor a b c S.toFinset := by
  have ss := hs.subset; have nd := hs.nodup (gp.nodup hs.length_le); simp [not_or] at ss nd
  rw [σIsEmptyTriangleFor_iff] <;> simp [*]

theorem σHasEmptyKGon_iff_HasEmptyKGon (gp : Point.ListInGenPos pts) :
    σHasEmptyKGon n pts.toFinset ↔ HasEmptyKGon n pts.toFinset := by
  unfold σHasEmptyKGon HasEmptyKGon
  refine exists_congr fun s => and_congr_right' <| and_congr_right fun spts => ?_
  rw [ConvexEmptyIn.iff_triangles'' spts gp]
  simp [Set.subset_def] at spts
  iterate 9 refine forall_congr' fun _ => ?_
  rw [σIsEmptyTriangleFor_iff gp] <;> simp [EmptyShapeIn, PtInTriangle, *]

lemma σPtInTriangle_congr (e : S ≃σ T) :
    ∀ (_ : a ∈ S) (_ : p ∈ S) (_ : q ∈ S) (_ : r ∈ S),
      σPtInTriangle (e.f a) (e.f p) (e.f q) (e.f r) ↔ σPtInTriangle a p q r := by
  simp (config := {contextual := true}) [σPtInTriangle, e.σ_eq]

theorem σHasEmptyKGon_3_iff (gp : Point.ListInGenPos pts) :
    σHasEmptyKGon 3 pts.toFinset ↔
      ∃ a b c, [a, b, c] <+~ pts ∧ σIsEmptyTriangleFor a b c pts.toFinset := by
  constructor
  · intro ⟨s, hs1, ss, hs2⟩
    match s, s.exists_mk with | _, ⟨[a,b,c], h1, rfl⟩ => ?_
    have sp := subperm_of_subset (l₂ := pts) h1 (by simpa [Set.subset_def] using ss)
    refine ⟨a, b, c, sp, fun p hp hn => ?_⟩
    have := (hs2 a · b · c ·)
    simp [not_or] at h1 hp; simp [h1] at this
    refine this _ ?_ hn
    simp [hp]
  · intro ⟨a, b, c, sp, H⟩
    have nd := sp.nodup (gp.nodup sp.length_le)
    have ⟨s, hs1, hs2⟩ : ∃ s : Finset Point, s = ⟨[a, b, c], nd⟩ ∧ s.card = 3 := ⟨_, rfl, rfl⟩
    refine ⟨s, hs2, by simpa [hs1, Set.subset_def] using sp.subset, ?_⟩
    intro x hx y hy z hz xy xz yz u hu hn
    simp [not_or] at hu
    refine H u (by simp [hu]) <| (σPtInTriangle.perm ?_).1 hn
    have : ⟨[x, y, z], by simp [*]⟩ = s :=
      Finset.eq_of_subset_of_card_le (by simp [Finset.subset_iff, hx, hy, hz]) (by simp [hs2])
    exact Multiset.coe_eq_coe.1 <| Finset.val_inj.2 <| this.trans hs1

lemma OrientationProperty_σHasEmptyKGon : OrientationProperty (σHasEmptyKGon n) := by
  unfold σHasEmptyKGon
  intro S T e ⟨s, scard, sS, h⟩
  refine ⟨s.image e, ?_, ?_, ?_⟩
  . rwa [s.card_image_of_injOn (e.bij.right.left.mono sS)]
  . intro x; simp
    rintro _ hx rfl
    exact e.bij.left (sS hx)
  . have injs : Set.InjOn e s := e.bij.right.left.mono sS
    simp (config := { contextual := true }) only [injs.eq_iff,
      Finset.mem_image, Finset.mem_coe, σIsEmptyTriangleFor,
      and_imp, forall_exists_index, forall_apply_eq_imp_iff₂, ne_eq, not_or,
      Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff] at h ⊢
    -- The part below is very explicit, maybe could be automated.
    intro a ha b hb c hc ab ac bc p hp
    have : e.symm p ∈ S := e.symm.bij.left hp
    have : p = e (e.symm p) := e.apply_symm_apply hp |>.symm
    rw [this, σPtInTriangle_congr e (e.symm.bij.left hp) (sS ha) (sS hb) (sS hc)]
    exact h a ha b hb c hc ab ac bc (e.symm p) (e.symm.bij.left hp)

theorem σIsEmptyTriangleFor_exists (gp : Point.ListInGenPos S)
    (abc : [a, b, c] <+~ S) :
    ∃ b' ∈ S, σ a b' c = σ a b c ∧ (b' = b ∨ σPtInTriangle b' a b c) ∧
      σIsEmptyTriangleFor a b' c S.toFinset := by
  have nd := gp.nodup abc.length_le
  have gp' := Point.ListInGenPos.subperm.1 gp
  have ss := abc.subset; simp at ss
  let _ : Preorder Point := {
    le := fun x y => PtInTriangle x a y c
    le_refl := fun z => subset_convexHull _ _ <| by simp
    le_trans := fun u v w uv vw => by
      simp [PtInTriangle] at uv vw ⊢
      refine convexHull_min ?_ (convex_convexHull ..) uv
      simp [Set.subset_def, *]; constructor <;> apply subset_convexHull <;> simp
  }
  have ⟨b', hb1, hb2⟩ := Finset.exists_minimal
    (S.toFinset.filter fun x => σ a x c = σ a b c ∧ x ≤ b)
    ⟨b, by simp [ss]; apply subset_convexHull; simp⟩
  simp at hb1 hb2
  have abc' : Point.InGenPos₃ a b' c := by
    rw [Point.InGenPos₃.iff_ne_collinear, hb1.2.1,
      ← Point.InGenPos₃.iff_ne_collinear]; exact gp' abc
  refine ⟨_, hb1.1, hb1.2.1, ?_, fun z hz hn => ?_⟩
  · refine or_iff_not_imp_left.2 fun h => ?_
    refine (σPtInTriangle_iff <| gp.subperm₄ ?_).2 hb1.2.2
    refine subperm_of_subset ?_ (List.cons_subset.2 ⟨hb1.1, abc.subset⟩)
    exact nodup_cons.2 ⟨by simp [not_or, h, abc'.ne₁.symm, abc'.ne₃], abc.nodup nd⟩
  simp at hz
  have gp4 := hn.gp₄_of_gp₃ abc'
  have zb' : z ≤ b' := (σPtInTriangle_iff gp4).1 hn
  have := (σPtInTriangle_iff gp4.perm₁.perm₂.perm₁).2 <|
    hb2 _ hz (by rw [hn.2.1, hb1.2.1]) (zb'.trans hb1.2.2) zb'
  refine Point.InGenPos₃.iff_ne_collinear.1 abc' <| (Orientation.eq_neg_self _).1 ?_
  rw [← neg_inj.2 hn.1, ← σ_perm₂, this.1, hn.2.1]

def σCCWPoints : List Point → Prop
  | [] => True
  | a :: l => l.Pairwise (σ a · · = .ccw) ∧ σCCWPoints l

theorem σCCWPoints_append : σCCWPoints (l₁ ++ l₂) ↔
    σCCWPoints l₁ ∧ σCCWPoints l₂ ∧
    (∀ a ∈ l₁, l₂.Pairwise (σ a · · = .ccw)) ∧
    (∀ c ∈ l₂, l₁.Pairwise (σ · · c = .ccw)) := by
  induction l₁ generalizing l₂ with | nil => simp [σCCWPoints] | cons a l₁ IH => ?_
  simp [σCCWPoints, pairwise_append, forall_and, IH]; aesop

theorem σCCWPoints.iff_sublist :
    σCCWPoints l ↔ ∀ {{p q r : Point}}, [p, q, r] <+ l → σ p q r = .ccw := by
  constructor <;> intro H
  · intro p q r ss
    induction l with
    | nil => cases ss
    | cons a l IH =>
      cases ss with
      | cons _ ss => exact IH H.2 ss
      | cons₂ _ ss => exact pairwise_iff_forall_sublist.1 H.1 ss
  · induction l with
    | nil => trivial
    | cons a l IH =>
      exact ⟨
        pairwise_iff_forall_sublist.2 fun ss => H (.cons₂ _ ss),
        IH fun _ _ _ ss => H (.cons _ ss)⟩

theorem σCCWPoints.sublist (H : σCCWPoints l') (ss : l <+ l') : σCCWPoints l :=
  σCCWPoints.iff_sublist.2 fun _ _ _ h => σCCWPoints.iff_sublist.1 H (h.trans ss)

theorem σCCWPoints.gp (H : σCCWPoints l) : Point.ListInGenPos l :=
  fun a b c ss => Point.InGenPos₃.iff_ne_collinear.2 <|
    σCCWPoints.iff_sublist.1 H ss ▸ by decide

theorem σCCWPoints.cycle (H : σCCWPoints (l₁ ++ l₂)) : σCCWPoints (l₂ ++ l₁) := by
  simp [σCCWPoints_append] at H ⊢
  let ⟨H1, H2, H3, H4⟩ := H
  exact ⟨H2, H1,
    fun c hc => (H4 c hc).imp <| Eq.trans (by rw [σ_perm₁, ← σ_perm₂]),
    fun a ha => (H3 a ha).imp <| Eq.trans (by rw [σ_perm₂, ← σ_perm₁])⟩

theorem σCCWPoints.convex (H : σCCWPoints l) : ConvexPoints l.toFinset := by
  refine ((ConvexEmptyIn.iff_triangles'' subset_rfl H.gp).2 ?_).1
  simp only [mem_toFinset, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton,
    not_or, and_imp]
  intro a ha b hb c hc ab ac bc p hp pa pb pc hn
  have ⟨l', lp, H⟩ : ∃ l', l ~ p::l' ∧ σCCWPoints (p::l') := by
    obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem hp
    exact ⟨l₂++l₁, perm_append_comm, σCCWPoints.cycle H⟩
  simp [lp.mem_iff, Ne.symm, pa, pb, pc] at ha hb hc
  have sp : [a, b, c] <+~ l' := by apply subperm_of_subset <;> simp [*]
  have := (σPtInTriangle_iff <| H.gp.subperm₄ (.cons₂ sp)).2 hn
  let ⟨l₂, hp, sp⟩ := sp
  match l₂, hp.length_eq with | [a, b, c], _ => ?_
  have apc := ((σPtInTriangle.perm hp).2 this).2.1
  have abc := σCCWPoints.iff_sublist.1 H.2 sp
  have pac := pairwise_iff_forall_sublist.1 H.1 (.trans (.cons₂ _ (.cons _ (.refl _))) sp)
  rw [σ_perm₁, apc, abc] at pac; cases pac

theorem σCCWPoints.split_l (H : σCCWPoints (a::l₁++b::l₂)) : σCCWPoints (a::l₁++[b]) :=
  H.sublist <| .append_left (.cons₂ _ <| nil_sublist _) _

theorem σCCWPoints.split_r (H : σCCWPoints (a::l₁++b::l₂)) : σCCWPoints (b::l₂++[a]) :=
  H.cycle.split_l

theorem EmptyShapeIn.perm {l₁ l₂ : List Point} (p : l₁ ~ l₂) :
    EmptyShapeIn l₁.toFinset P ↔ EmptyShapeIn l₂.toFinset P := by simp [p.mem_iff]

theorem σCCWPoints.split_emptyShapeIn (a l₁ b l₂) (H : σCCWPoints (a::l₁++b::l₂))
    (H1 : EmptyShapeIn (a::l₁++[b]).toFinset P)
    (H2 : EmptyShapeIn (b::l₂++[a]).toFinset P) :
    EmptyShapeIn (a::l₁ ++ b::l₂).toFinset P := by
  have h1 {c} (hc : c ∈ l₁) : σ a b c = .cw := by
    rw [σ_perm₂, (pairwise_cons.1 ((σCCWPoints_append.1 H).2.2.2 _ (.head _))).1 _ hc]; rfl
  have h2 {c} (hc : c ∈ l₂) : σ a b c = .ccw :=
    (pairwise_cons.1 ((σCCWPoints_append.1 H).2.2.1 _ (.head _))).1 _ hc
  refine EmptyShapeIn.split (a := a) (b := b) H.convex (by simp) (by simp) ?_ ?_
  · convert H1 using 1; ext x; simp
    refine (and_congr_left fun h => ?_).trans (and_iff_left_of_imp ?_)
    · refine or_congr_right <| or_congr_right <| or_iff_left <| mt h2 h
    · rintro (rfl | rfl | h) <;> simp [σ_self₁, σ_self₂, *]
  · convert H2 using 1; ext x; simp
    refine (and_congr_left fun h => ?_).trans (and_iff_left_of_imp ?_)
    · refine or_left_comm.trans <| or_congr_right <| or_congr_right <| or_iff_right <| mt h1 h
    · rintro (rfl | rfl | h) <;> simp [σ_self₁, σ_self₂, *]

theorem σCCWPoints.flatten (H : σCCWPoints (a::b::c::l)) (gp : Point.ListInGenPos S)
    (sp : a::b::c::l <+~ S) :
    ∃ b', a::b'::c::l <+~ S ∧ σCCWPoints (a::b'::c::l) ∧
      EmptyShapeIn [a, b', c].toFinset S.toFinset := by
  have sp' := (sublist_append_left [a, b, c] l).subperm.trans sp
  obtain ⟨b', hb', ab'c, h1, h2⟩ := σIsEmptyTriangleFor_exists gp sp'
  by_cases bb : b' = b
  · subst bb; exact ⟨b', sp, H, (σIsEmptyTriangleFor_iff' gp sp').2 h2⟩
  replace h1 := h1.resolve_left bb
  have abc := σCCWPoints.iff_sublist.1 H (sublist_append_left _ l)
  rw [abc] at ab'c
  have ndS := gp.nodup sp'.length_le
  have ss := sp.subset; have nd := sp.nodup (gp.nodup sp'.length_le); simp [not_or] at ss nd
  have nd' : b' ∉ a :: b :: c :: l := by
    have gp3 := H.gp (sublist_append_left _ l)
    rintro (_|⟨_, _|⟨_, _|⟨_, h : b' ∈ l⟩⟩⟩)
    · exact not_mem_σPtInTriangle gp3.perm₁ h1.perm₁
    · exact not_mem_σPtInTriangle gp3 h1
    · exact not_mem_σPtInTriangle gp3.perm₂ h1.perm₂
    · rw [σ_perm₂, σCCWPoints.iff_sublist.1 H] at ab'c; cases ab'c
      exact .cons₂ _ <| .cons _ <| .cons₂ _ <| singleton_sublist.2 h
  have sp4 : b' :: a :: b :: c :: l <+~ S :=
    subperm_of_subset (nodup_cons.2 ⟨nd', sp.nodup ndS⟩) (cons_subset.2 ⟨hb', sp.subset⟩)
  have sp3 : a :: b' :: c :: l <+~ S :=
    .trans ⟨_, .swap .., .cons₂ _ <| .cons₂ _ <| .cons _ <| .refl _⟩ sp4
  refine ⟨b', sp3, ?_, (σIsEmptyTriangleFor_iff' gp <|
    (sublist_append_left _ l).subperm.trans sp3).2 h2⟩
  have gp3 := gp.mono_subperm sp3
  have cvx {e f} (sp : [e, f, b'] <+~ a::b'::c::l)
      (ss : σ e f a ≠ .cw ∧ σ e f b ≠ .cw ∧ σ e f c ≠ .cw) : σ e f b' = .ccw := by
    rw [← (Point.ListInGenPos.subperm.1 gp3 sp).σ_iff']
    rw [σ, Ne, Orientation.ofReal_eq_cw, not_lt]
    refine convexHull_min ?_ ((convex_Ici 0).affine_preimage (detAffineMap e f)) <|
      (σPtInTriangle_iff (gp.subperm₄ ((sublist_append_left _ l).subperm.trans sp4))).1 h1
    replace ss : ∀ d ∈ ({a, b, c}:Set _), σ e f d ≠ .cw := by simpa using ss
    intro d hd
    simpa [σ, Orientation.ofReal_eq_cw] using ss d hd
  simp [σCCWPoints] at H; simp [H, ab'c, σCCWPoints]
  obtain ⟨⟨⟨-, abd⟩, acd, ade⟩, ⟨bcd, bde⟩, cde, -⟩ := H
  refine ⟨⟨fun d hd => ?_, acd⟩, fun d hd => ?_, ?_⟩
  · rw [σ_perm₂, ← σ_perm₁]
    refine cvx ⟨_, @perm_append_comm _ [a, b'] [d],
      .append_left (.cons _ (by simp [hd])) [a,b']⟩ ⟨?_, ?_, ?_⟩
    · simp [σ_self₁]
    · rw [σ_perm₁, ← σ_perm₂, abd _ hd]; decide
    · rw [σ_perm₁, ← σ_perm₂, acd _ hd]; decide
  · rw [σ_perm₁, ← σ_perm₂]
    refine cvx ⟨_, @perm_append_comm _ [b'] [c, d],
      .cons _ <| .cons₂ _ <| .cons₂ _ (by simp [hd])⟩ ⟨?_, ?_, ?_⟩
    · rw [σ_perm₂, ← σ_perm₁, acd _ hd]; decide
    · rw [σ_perm₂, ← σ_perm₁, bcd _ hd]; decide
    · simp [σ_self₂]
  · rw [pairwise_iff_forall_sublist] at ade bde cde ⊢
    intro d e de
    rw [σ_perm₁, ← σ_perm₂]
    refine cvx ⟨_, @perm_append_comm _ [b'] [d, e],
      .cons _ <| .cons₂ _ <| .cons _ de⟩ ⟨?_, ?_, ?_⟩
    · rw [σ_perm₂, ← σ_perm₁, ade de]; decide
    · rw [σ_perm₂, ← σ_perm₁, bde de]; decide
    · rw [σ_perm₂, ← σ_perm₁, cde de]; decide

theorem σCCWPoints.emptyHexagon
    (H : σCCWPoints [a, b, c, d, e, f]) (gp : Point.ListInGenPos S)
    (hole : σIsEmptyTriangleFor a c e S.toFinset) (sp : [a, b, c, d, e, f] ⊆ S) :
    σHasEmptyKGon 6 S.toFinset := by
  have sp := subperm_of_subset (H.gp.nodup (by show 3 ≤ 6; decide)) sp
  have hole := (σIsEmptyTriangleFor_iff' gp <|
    .trans (.cons₂ <| .cons <| .cons₂ <| .cons <| .cons₂ nil_subperm) sp).2 hole
  have ⟨b', sp, H, abc⟩ := σCCWPoints.flatten H gp sp
  have ⟨d', sp, H, cde⟩ := σCCWPoints.flatten (H.cycle (l₁ := [a, b']) (l₂ := [c,d,e,f]))
    gp ((@perm_append_comm _ [c,d,e,f] [a, b']).subperm.trans sp)
  have ⟨f', sp, H, efa⟩ := σCCWPoints.flatten (H.cycle (l₁ := [c, d']) (l₂ := [e,f,a,b']))
    gp ((@perm_append_comm _ [e,f,a,b'] [c, d']).subperm.trans sp)
  refine (σHasEmptyKGon_iff_HasEmptyKGon gp).2
    ⟨[e, f', a, b', c, d'].toFinset, ?_, by simpa [Set.subset_def] using sp.subset, H.convex, ?_⟩
  · exact congrArg length (dedup_eq_self.2 (H.gp.nodup (by show 3 ≤ 6; decide)))
  · refine σCCWPoints.split_emptyShapeIn e [f'] a [b', c, d'] H efa ?_
    have H := H.split_r (l₁ := [f'])
    refine σCCWPoints.split_emptyShapeIn a [b'] c [d', e] H abc ?_
    have H := H.split_r (l₁ := [b'])
    refine σCCWPoints.split_emptyShapeIn c [d'] e [a] H cde ?_
    refine (EmptyShapeIn.perm <| @perm_append_comm _ [a, c] [e]).1 hole

theorem σCCWPoints.emptyHexagon'
    (H : σCCWPoints [a, b, c, d, e, f]) (gp : Point.ListInGenPos S)
    (hole : σIsEmptyTriangleFor b d f S.toFinset) (sp : [a, b, c, d, e, f] ⊆ S) :
    σHasEmptyKGon 6 S.toFinset :=
  σCCWPoints.emptyHexagon (H.cycle (l₁ := [a])) gp hole <|
    (@perm_append_comm _ _ [a]).subset.trans sp

end Geo
