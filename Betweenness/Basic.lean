import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice

open Set

class Between (α : Type u) where
  between : α → α → α → Prop
  refl : ∀ {a b}, between a b b
  symm : ∀ {a b c}, between a b c → between c b a
  extend : ∀ {a b x y z}, between a x b → between a y b → between x z y → between a z b
  antisymm : ∀ {a b c}, between a b c → between a c b → b = c

namespace Between

variable {α : Type u} [Between α]

theorem refl_left {a b : α} : between a a b := symm refl

theorem trans {a b c d : α} (h : between a b c) (h' : between a c d) : between a b d
  := extend refl_left h' h

theorem trans_left {a b c d : α} (h : between a b d) (h' : between b c d) : between a c d
  := symm (trans (symm h') (symm h))

theorem antisymm_left {a b c : α} (h : between a b c) (h' : between b a c) : a = b
  := antisymm (symm h') (symm h)

theorem antisymm_outer {a b : α} (h : between a b a) : a = b := antisymm refl_left h

theorem antisymm_outer_iff {a b : α} : between a b a ↔ a = b := ⟨antisymm_outer, λ| rfl => refl⟩

theorem symm_iff {a b c : α} : between a b c ↔ between c b a := Iff.intro symm symm

def seg (a b : α) : Set α := { x | between a x b }

theorem seg_comm {a b : α} : seg a b = seg b a := by ext x; constructor <;> apply symm

theorem seg_self {a : α} : seg a a = {a} := by ext x; simp [seg, antisymm_outer_iff]

theorem left_mem_seg {a b : α} : a ∈ seg a b := refl_left

theorem right_mem_seg {a b : α} : b ∈ seg a b := refl

theorem subseg {a b x y : α} (hx : x ∈ seg a b) (hy : y ∈ seg a b) : seg x y ⊆ seg a b
  := λ_ hz => extend hx hy hz

theorem union_subseg {a b x y : α} (hx : x ∈ seg a b) (hy : y ∈ seg a b)
  : seg x y ∪ seg a b = seg a b := union_eq_self_of_subset_left (subseg hx hy)

theorem subseg_union {a b x y : α} (hx : x ∈ seg a b) (hy : y ∈ seg a b)
  : seg a b ∪ seg x y = seg a b := union_eq_self_of_subset_right (subseg hx hy)

def cone (a : α) (A : Set α) : Set α := ⋃x ∈ A, seg a x

theorem cone_empty {a : α} : cone a ∅ = ∅ := by simp [cone]

theorem cone_point {a b : α} : cone a {b} = seg a b := by simp [cone]

theorem cone_pair {a b c : α} : cone a {b, c} = seg a b ∪ seg a c := by simp [cone]

theorem cone_insert {a : α} {A : Set α} {b : α} : cone a (insert b A) = seg a b ∪ cone a A := by
  simp [cone]

theorem tip_mem_cone {a : α} {A : Set α} (h : Nonempty A) : a ∈ cone a A := by
  simp only [cone, mem_iUnion, exists_prop]
  have ⟨b, hb⟩ := h
  exact ⟨b, hb, left_mem_seg⟩

theorem insert_tip_cone {a : α} {A : Set α} (h : Nonempty A) : insert a (cone a A) = cone a A
  := insert_eq_of_mem (tip_mem_cone h)

theorem cone_mono {a : α} {A B : Set α} (h : A ⊆ B) : cone a A ⊆ cone a B
  := biUnion_mono h (λ_ _ => Subset.rfl)

theorem cone_union {a : α} {A B : Set α} : cone a (A ∪ B) = cone a A ∪ cone a B := by
  simp only [cone, biUnion_union]

def ray' (a b : α) : Set α := { x | between x a b }

theorem ray_self' {a : α} : ray' a a = univ := by ext x; simp [ray', refl]

def ray (a b : α) : Set α := { x | between x a b ∧ a ≠ b }

theorem ray_self {a : α} : ray a a = ∅ := by ext x; simp [ray]

theorem ray_subset_ray' {a b : α} : ray a b ⊆ ray' a b := λ_ ⟨h, _⟩ => h

def rayTo (a b : α) : Set α := seg a b ∪ ray b a

theorem seg_subset_rayTo {a b : α} : seg a b ⊆ rayTo a b := by simp [rayTo]

theorem seg_subset_rayTo' {a b : α} : seg b a ⊆ rayTo a b := by rw [seg_comm]; simp [rayTo]

theorem ray_subset_rayTo {a b : α} : ray b a ⊆ rayTo a b := by simp [rayTo]

theorem seg_union_rayTo {a b : α} : seg a b ∪ rayTo a b = rayTo a b := by
  simp [rayTo]

theorem rayTo_union_seg {a b : α} : rayTo a b ∪ seg a b = rayTo a b := by
  simp [rayTo]

theorem seg_union_rayTo' {a b : α} : seg b a ∪ rayTo a b = rayTo a b := by
  rw [seg_comm, seg_union_rayTo]

theorem rayTo_union_seg' {a b : α} : rayTo a b ∪ seg b a = rayTo a b := by
  rw [seg_comm, rayTo_union_seg]

def line (a b : α) : Set α := ray a b ∪ seg a b ∪ ray b a

theorem line_comm {a b : α} : line a b = line b a := by
  rw [line, seg_comm, line, union_comm, union_assoc]; congr 1; rw [union_comm]

theorem line_self {a : α} : line a a = {a} := by simp [line, ray_self, seg_self]

theorem left_mem_line {a b : α} : a ∈ line a b := by simp [line, left_mem_seg]

theorem right_mem_line {a b : α} : b ∈ line a b := by simp [line, right_mem_seg]

theorem line_eq_union_rayTo {a b : α} : line a b = rayTo b a ∪ rayTo a b := by
  rw [
    rayTo, rayTo, union_comm (a := seg b a), union_assoc, <-union_assoc (a := seg b a), seg_comm,
    union_self, <-union_assoc, line
  ]

def Colinear (A : Set α) := ∃a b, A ⊆ line a b

theorem colinear_empty [Nonempty α] : Colinear (∅ : Set α)
  := ⟨Classical.ofNonempty, Classical.ofNonempty, empty_subset _⟩

theorem colinear_singleton {a : α} : Colinear {a} := ⟨a, a, by simp [line_self]⟩

theorem colinear_pair {a b : α} : Colinear {a, b} := ⟨a, b,
  λx h => by cases h <;> rename_i h <;> cases h <;> simp [left_mem_line, right_mem_line]⟩

theorem rayTo_subset_line {a b : α} : rayTo a b ⊆ line a b := by
  rw [line_eq_union_rayTo]; simp

theorem rayTo_subset_line' {a b : α} : rayTo b a ⊆ line a b := by
  rw [line_eq_union_rayTo]; simp

theorem seg_subset_line {a b : α} : seg a b ⊆ line a b
  := subset_trans seg_subset_rayTo rayTo_subset_line

theorem seg_subset_line' {a b : α} : seg b a ⊆ line a b
  := subset_trans seg_subset_rayTo' rayTo_subset_line

def angle (a o b : α) : Set α := rayTo o a ∪ rayTo o b

def triangle (a b c : α) : Set α := seg a b ∪ seg b c ∪ seg c a

theorem triangle_dup_left {a b : α} : triangle a a b = seg a b := by
  simp [triangle, union_subseg left_mem_seg left_mem_seg, seg_comm]

theorem triangle_self {a : α} : triangle a a a = {a} := by rw [triangle_dup_left, seg_self]

theorem triangle_cycle {a b c : α} : triangle a b c = triangle b c a := by rw [
  triangle, triangle, union_comm (a := seg a b), union_assoc, union_comm (a := seg a b), union_assoc
]

theorem triangle_comm_right {a b c : α} : triangle a b c = triangle a c b := by
  rw [triangle, triangle, seg_comm, union_assoc, union_comm]
  congr 1
  rw [union_comm, seg_comm, seg_comm (a := b)]

theorem triangle_comm_left {a b c : α} : triangle a b c = triangle b a c := by
  rw [triangle_cycle, triangle_comm_right]

theorem triangle_cycle2 {a b c : α} : triangle a b c = triangle c a b := by
  rw [triangle_cycle, triangle_cycle]

theorem triangle_dup_outer {a b : α} : triangle a b a = seg a b := by
  rw [triangle_comm_right, triangle_dup_left]

theorem triangle_dup_right {a b : α} : triangle a b b = seg a b := by
  rw [triangle_comm_left, triangle_dup_outer, seg_comm]

def triangle2 (a b c : α) : Set α := cone a (seg b c)

theorem triangle2_self {a : α} : triangle2 a a a = {a} := by simp [triangle2, seg_self, cone_point]

-- TODO: triangle2 cyclic lore

def tetrahedron1 (a b c d : α) : Set α
  := triangle a b c ∪ triangle a b d ∪ triangle a c d ∪ triangle b c d

def tetrahedron2 (a b c d : α) : Set α
  := triangle2 a b c ∪ triangle2 a b d ∪ triangle2 a c d ∪ triangle2 b c d

def tetrahedron3 (a b c d : α) : Set α := cone a (triangle2 b c d)

def surface (A : Set α) (B : Set α) : Set α := ⋃x ∈ A, ⋃y ∈ B, seg x y

theorem surface_subset_comm {A B : Set α} : surface A B ⊆ surface B A := by
  intro x
  simp only [surface, mem_iUnion, exists_prop, forall_exists_index, and_imp]
  intro a ha b hb hx
  exact ⟨b, hb, a, ha, seg_comm (a := a) (b := b) ▸ hx⟩

theorem surface_comm {A B : Set α} : surface A B = surface B A
  := Subset.antisymm surface_subset_comm surface_subset_comm

theorem surface_empty_left {A : Set α} : surface ∅ A = ∅ := by simp [surface]

theorem surface_empty {A : Set α} : surface A ∅ = ∅ := by simp [surface]

theorem surface_point_left {A} {a : α} : surface {a} A = cone a A := by simp [surface, cone]

theorem surface_point {A} {a : α} : surface A {a} = cone a A
  := by rw [surface_comm, surface_point_left]

theorem surface_points {a b : α} : surface {a} {b} = seg a b := by simp [surface]

theorem surface_pair_left {A} {a b : α} : surface {a, b} A = cone a A ∪ cone b A := by
  simp [surface, cone]

theorem surface_pair {A} {a b : α} : surface A {a, b} = cone a A ∪ cone b A
  := by rw [surface_comm, surface_pair_left]

theorem surface_mono {A B C D : Set α} (hA : A ⊆ C) (hB : B ⊆ D) : surface A B ⊆ surface C D
  := biUnion_mono hA (λ_ _ => biUnion_mono hB (λ_ _ => Subset.rfl))

theorem surface_union_left {A B C : Set α} : surface (A ∪ B) C = surface A C ∪ surface B C := by
  simp only [surface, biUnion_union]

theorem surface_union {A B C : Set α} : surface A (B ∪ C) = surface A B ∪ surface A C := by
  rw [surface_comm, surface_union_left]; simp [surface_comm]

theorem surface_insert_left {A B : Set α} {a : α}
  : surface (insert a A) B = cone a B ∪ surface A B := by simp [surface, cone]

theorem surface_insert {A B : Set α} {a : α}
  : surface A (insert a B) = cone a A ∪ surface A B := by
  rw [surface_comm, surface_insert_left, surface_comm]

def fill (A : Set α) : Set α := surface A A

theorem fill_empty : fill (∅ : Set α) = ∅ := by simp [fill, surface_empty]

theorem fill_point {a : α} : fill {a} = {a} := by simp [fill, surface, seg_self]

theorem fill_insert {A : Set α} {a : α} : fill (insert a A) = insert a (cone a A) ∪ fill A := by
  rw [
    fill, surface_insert, surface_insert_left, cone_insert, seg_self, union_assoc,
    <-union_assoc (a := cone a A), union_self, <-union_assoc
  ]
  rfl

theorem fill_insert' {A : Set α} {a : α} (h : Nonempty A) : fill (insert a A) = cone a A ∪ fill A
  := by rw [fill_insert, insert_tip_cone h]

theorem fill_pair {a b : α} : fill {a, b} = seg a b := by
  rw [fill_insert' (by simp), cone_point, fill_point, union_eq_self_of_subset_right]
  simp [right_mem_seg]

theorem fill_triple {a b c : α} : fill {a, b, c} = triangle a b c := by
  rw [
    fill_insert' (by simp), cone_pair, fill_pair, triangle, union_assoc, union_comm (a := seg a c),
    union_assoc, seg_comm (a := c)
  ]

theorem fill_mono {A B : Set α} (h : A ⊆ B) : fill A ⊆ fill B := surface_mono h h

theorem fill_union {A B : Set α} : fill (A ∪ B) = fill A ∪ surface A B ∪ fill B := by
  rw [fill, surface_union, surface_union_left, surface_union_left, fill, union_assoc, union_assoc]
  congr 1
  rw [<-union_assoc, surface_comm, union_self]
  rfl

def castTo (a : α) (A : Set α) : Set α := ⋃x ∈ A, rayTo a x

theorem cone_subset_castTo {a : α} {A : Set α} : cone a A ⊆ castTo a A
  := biUnion_mono Subset.rfl (λ_ _ => seg_subset_rayTo)

def castFrom (a : α) (A : Set α) : Set α := ⋃x ∈ A, ray x a

theorem castFrom_subset_castTo {a : α} {A : Set α} : castFrom a A ⊆ castTo a A
  := biUnion_mono Subset.rfl (λ_ _ => ray_subset_rayTo)

def castThrough (a : α) (A : Set α) : Set α := ⋃x ∈ A, rayTo x a

def castAway (a : α) (A : Set α) : Set α := ⋃x ∈ A, ray a x

def lines (a : α) (A : Set α) : Set α := ⋃x ∈ A, line a x

def sweep (A : Set α) (B : Set α) : Set α := ⋃x ∈ A, ⋃y ∈ B, line x y

theorem surface_subset_sweep {A B : Set α} : surface A B ⊆ sweep A B
  := Set.biUnion_mono Set.Subset.rfl
    (λ_ _ => Set.biUnion_mono Set.Subset.rfl (λ_ _ => seg_subset_line))

def radiate (A : Set α) : Set α := sweep A A

theorem fill_subset_radiate {A : Set α} : fill A ⊆ radiate A := surface_subset_sweep

def plane (a b c : α) : Set α := radiate (triangle a b c)

def space (a b c d : α) : Set α := radiate (tetrahedron2 a b c d)

-- TODO: define circles, is this enough for Euclid?

end Between

open Between

-- NOTE: identity does not need to be an iff if we have segment construction; but that requires
-- us to have a notion of betweenness

class SegCongruence (α : Type u) where
  scongr : α → α → α → α → Prop
  flip : ∀{a b}, scongr a b b a
  identity_iff : ∀{a b c}, scongr a a b c ↔ b = c
  trans : ∀{a b c d e f}, scongr a b c d → scongr c d e f → scongr a b e f
  symm : ∀{a b c d}, scongr a b c d → scongr c d a b

namespace SegCongruence

variable {α : Type u} [SegCongruence α]

theorem refl {a b : α} : scongr a b a b
  := trans flip flip

theorem identity {a b c : α} (h : scongr a a b c) : b = c := identity_iff.mp h

theorem symm_iff {a b c d : α} : scongr a b c d ↔ scongr c d a b := ⟨symm, symm⟩

theorem identity_left_iff {a b c : α} : scongr a b c c ↔ a = b := by rw [symm_iff, identity_iff]

theorem identity_left {a b c : α} (h : scongr a b c c) : a = b := identity_left_iff.mp h

def ball (a b : α) : Set α := { x | scongr a b a x }

theorem ball_self {a : α} : ball a a = {a}
  := Set.ext (λ_ => ⟨λh => (identity h).symm, λ| rfl => refl⟩)

end SegCongruence

open SegCongruence

class Between.Pasch (α : Type u) [Between α] where
  pasch : ∀{a b c x y : α}, between a x b → between a y c → ∃z, between x z b ∧ between y z a

class Between.Flat (α : Type u) [Between α] where
  flat : ∀{x y z u v : α}, between x u v → between y u z → x ≠ u
    → ∃a, ∃b, between x y a ∧ between x z b ∧ between a v b

-- TODO: find cleaner characterization
-- TODO: check
class Between.Hyperbolic (α : Type u) [Between α] where
  hyperbolic : ∀{x y z u v : α}, ¬(between x u v → between y u z → x ≠ u
    → ∃a, ∃b, between x y a ∧ between x z b ∧ between a v b)

-- TODO: find characterization of spherical geometry?

class Between.SAS (α : Type u) [Between α] [SegCongruence α] where
  sas : ∀{x y z u x' y' z' u' : α},
    x ≠ y → between x y z → between x' y' z'
      → scongr x y x' y'
      → scongr y z y' z'
      → scongr x u x' u'
      → scongr y u y' u'
      → scongr z u z' u'

class Between.Construct (α : Type u) [Between α] [SegCongruence α] where
  segcst : ∀{a b x y : α}, ∃z, between x y z  ∧ scongr y z a b

class Between.Cut (α : Type u) [Between α] where
  cut : ∀φ : Set α, ∀ψ : Set α,
    (∃a, ∀x, ∀y, x ∈ φ ∧ y ∈ ψ → between a x y) → ∃b, ∀x, ∀y, x ∈ φ ∧ y ∈ ψ → between x b y
