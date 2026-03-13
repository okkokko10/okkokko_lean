import Mathlib

variable {ι : Type*} [Fintype ι] [DecidableEq ι] --(B : Basis ι)


-- lemma wDiscreteTopology.of_forall_le_dist {α} [PseudoMetricSpace α] {r : ℝ} (hpos : 0 < r)
--     (hr : Pairwise (r ≤ dist · · : α → α → Prop)) : DiscreteTopology α := by
--     constructor
--     rw [Metric.uniformSpace_eq_bot.2 ⟨r, hpos, hr⟩, UniformSpace.toTopologicalSpace_bot]



  -- -- looked at the definition of [DiscreteTopology.of_forall_le_norm]
  -- -- and found [Metric.uniformSpace_eq_bot]
  -- #check Metric.uniformSpace_eq_bot
  -- -- studying [DiscreteTopology.of_forall_le_dist]

  -- have : ∃r, (0 < r) ∧ (Pairwise (r ≤ dist · · : Λ → Λ → Prop)) := by
  --   apply (Metric.uniformSpace_eq_bot (α := Λ)).mp
  --   have un := UniformSpace.toTopologicalSpace_bot (α := Λ)


  --   have ww:= DiscreteTopology.eq_bot (α := Λ)

  --   rw [←ww] at un
  --   simp_all

  -- --   rw [Metric.uniformSpace_eq_bot.2 ⟨r, hpos, hr⟩, UniformSpace.toTopologicalSpace_bot]
  -- -- have := Metric.uniformSpace_eq_bot (α := Λ).mp (by



  --   -- )



-- examining DiscreteTopology
example (Λ : Set (ι → ℝ)) [inst: DiscreteTopology ↥Λ] : False := by

  set_option trace.Meta.synthInstance true in
  set_option pp.instances true in

  let tp : TopologicalSpace Λ := by
    apply instTopologicalSpaceSubtype (t:= ?_)
    apply Pi.topologicalSpace
      (t₂ := ?_)
    intro i
    exact PseudoMetricSpace.toUniformSpace.toTopologicalSpace




  let tp' : TopologicalSpace Λ := by
    apply instTopologicalSpaceSubtype (t:= ?_)
    apply PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  have : tp = tp' := by rfl

  let dis : DiscreteTopology Λ (t := tp) := inferInstance
  let dis' : DiscreteTopology Λ (t := tp') := inferInstance
  have : dis = dis' := rfl
  have : inst = dis := rfl

  let tp'' : TopologicalSpace Λ := by
    apply @UniformSpace.toTopologicalSpace _ ?_
    apply @PseudoMetricSpace.toUniformSpace _ ?_
    exact Subtype.pseudoMetricSpace
  have : tp = tp'' := rfl


  have : ∃r, (0 < r) ∧ (Pairwise (r ≤ dist · · : Λ → Λ → Prop)) := by
    apply (Metric.uniformSpace_eq_bot (α := Λ)).mp
    have un := UniformSpace.toTopologicalSpace_bot (α := Λ)

    set s : UniformSpace Λ := ⊥

    set us : UniformSpace Λ := PseudoMetricSpace.toUniformSpace

    have us_bot : us.toTopologicalSpace = ⊥ := DiscreteTopology.eq_bot
    have : us.toTopologicalSpace = s.toTopologicalSpace := by
      rw [un, us_bot]
    refine UniformSpace.uniformSpace_eq_bot.mpr ?_
    rw [show uniformity ↥Λ = Filter.comap (fun p ↦ (↑p.1, ↑p.2)) (uniformity (ι → ℝ)) from rfl]


    -- refine UniformSpace.uniformSpace_eq_bot.mp ?_



    -- have : tp'' = s.toTopologicalSpace := by rfl
    -- have : tp' = instTopologicalSpaceSubtype (t := s.toTopologicalSpace) := by rfl
    sorry







  sorry
