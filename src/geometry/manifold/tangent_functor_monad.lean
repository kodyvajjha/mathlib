import geometry.manifold.basic_smooth_bundle

noncomputable theory

universes u v w


section tangent_bundle_monad

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
{E : Type*} [normed_group E] [normed_space 𝕜 E]
{H : Type*} [topological_space H] (I : model_with_corners 𝕜 E H)
(M : Type*) [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]


/-- The zero section is the `pure` of the tangent bundle monad. -/
def tangent_bundle.pure : M → tangent_bundle I M  :=
λ x, ⟨x,0⟩

/-- The zero section is a retraction of the projection. -/
@[simp] lemma pure_section :
∀ x, (tangent_bundle.proj I M) (tangent_bundle.pure I M x) = x := λ _, rfl

/-- The `join` operation of the tangent bundle monad.
    ⟨x,x',v,v'⟩ ↦ ⟨x,v⟩ and ⟨x,x',v,v'⟩ ↦ ⟨x,v⟩ satisfies one of the two unit laws. Their sum satisfies both.  -/
def tangent_bundle.join :
 tangent_bundle I.tangent (tangent_bundle I M) → tangent_bundle I M :=
λ ⟨⟨x, x'⟩, v, v'⟩, ⟨x, (v + x')⟩



end tangent_bundle_monad
