import geometry.manifold.basic_smooth_bundle
import geometry.manifold.mfderiv

noncomputable theory

universes u v w


section tangent_bundle_monad

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
{E E' : Type*} [normed_group E] [normed_group E'] [normed_space 𝕜 E] [normed_space 𝕜 E']
{H H' : Type*} [topological_space H] [topological_space H'] (I : model_with_corners 𝕜 E H)
(I' : model_with_corners 𝕜 E' H')
(M M': Type*) [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M][topological_space M'] [charted_space H' M'] [smooth_manifold_with_corners I' M']

/-- The zero section is the `pure` of the tangent bundle monad. -/
def tangent_bundle.pure : M → tangent_bundle I M  :=
λ x, ⟨x,0⟩

lemma tangent_map_tangent_bundle_pure :
  ∀ x v,
  tangent_map I I.tangent (tangent_bundle.pure I M) ⟨x,v⟩ = ⟨⟨x,0⟩,⟨v,0⟩⟩ :=
begin
  intros x v,
  simp [tangent_bundle.pure,tangent_map],
  dsimp,
  sorry,
end


/-- The zero section is a retraction of the projection. -/
@[simp] lemma pure_section :
∀ x, (tangent_bundle.proj I M) (tangent_bundle.pure I M x) = x := λ _, rfl

/-- The `join` operation of the tangent bundle monad.
    ⟨x,x',v,v'⟩ ↦ ⟨x,x'⟩ and ⟨x,x',v,v'⟩ ↦ ⟨x,v⟩ satisfies one of the two unit laws. Their sum satisfies both.  -/
def tangent_bundle.join :
 tangent_bundle I.tangent (tangent_bundle I M) → tangent_bundle I M :=
λ ⟨⟨x, x'⟩, v, v'⟩, ⟨x, (v + x')⟩


def tangent_bundle.bind :
tangent_bundle I M → (M → tangent_bundle I' M') → tangent_bundle I' M' :=
λ m f, tangent_bundle.join I' M' (tangent_map I I'.tangent f m)

lemma tangent_bundle.join_pure_1 :
∀ x',
tangent_bundle.join I M (tangent_bundle.pure I.tangent (tangent_bundle I M) x') = x' :=
begin
  rintros ⟨x,v⟩,
  unfold tangent_bundle.pure,
  have : (0 : tangent_space I.tangent (sigma.mk x v)) = ⟨0,0⟩, by refl,
  rw this,
  simp [tangent_bundle.join],
end

lemma tangent_bundle.join_pure_2 :
∀ x' : tangent_bundle I M,
tangent_bundle.join I M (tangent_map _ _ (tangent_bundle.pure I M) x') = x' :=
begin
  rintros ⟨x,v⟩,
  rw tangent_map_tangent_bundle_pure,
  dsimp [tangent_bundle.join],
  simp,
end

end tangent_bundle_monad
