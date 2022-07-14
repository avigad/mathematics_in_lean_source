.. index:: normed space

.. _normed_spaces:

Normed spaces
------------------------


.. code-block:: lean

  variables {E : Type*} [normed_group E] 
  
  example (x : E) : 0 ≤ ∥x∥ := 
  norm_nonneg x
  
  example {x : E} : ∥x∥ = 0 ↔ x = 0 := 
  norm_eq_zero
  
  example (x y : E) : ∥x + y∥ ≤ ∥x∥ + ∥y∥ := 
  norm_add_le x y
  
  variables [normed_space ℝ E] 
  
  example (a : ℝ) (x : E) : ∥a • x∥ = |a| * ∥x∥ :=
  norm_smul a x
  
  example [finite_dimensional ℝ E]: complete_space E :=
  by apply_instance
  

Continuous linear maps
^^^^^^^^^^^^^^^^^^^^^^


.. code-block:: lean

  variables {F : Type*} [normed_group F] [normed_space ℝ F]
  
  example : E →L[ℝ] E := continuous_linear_map.id ℝ E
  
  variables (f : E →L[ℝ] F)
  
  example : continuous f := 
  f.cont
  
  example (x : E) : ∥f x∥ ≤ ∥f∥ * ∥x∥ :=
  f.le_op_norm x


Derivatives
^^^^^^^^^^^

Lean can automatically compute some simple derivatives using `simp` tactic.

.. code-block:: lean

  example : deriv (λ x : ℝ, x^5) 6 = 5 * 6^4 := sorry
  
  example (x₀ : ℝ) (h₀ : x₀ ≠ 0) : deriv (λ x:ℝ, 1 / x) x₀ = -1 / x₀^2 := sorry
  
  example : deriv sin π = -1 := sorry
  
  -- Sometimes you need `ring` and/or `field_simp` after `simp`
  example (x₀ : ℝ) (h : x₀ ≠ 0) :
    deriv (λ x : ℝ, exp(x^2) / x^5) x₀ = (2 * x₀^2 - 5) * exp (x₀^2) / x₀^6 :=
  begin
    have : x₀^5 ≠ 0, { sorry },
    simp [this],
    sorry
  end
  
  example (a b x₀ : ℝ) (h : x₀ ≠ 1) :
    deriv (λ x, (a * x + b) / (x - 1)) x₀ = -(a + b) / (x₀ - 1)^2 :=
  begin
    sorry
  end
  
  
  
  
  #check deriv
  
  #check has_fderiv_at
  
  
  example (y : ℝ) : has_deriv_at (λ x : ℝ, 2 * x + 5) 2 y :=
  begin
    have := ((has_deriv_at_id y).const_mul 2).add_const 5,
    rwa [mul_one] at this,
  end
  
  example (y : ℝ) : deriv (λ x : ℝ, 2 * x + 5) y = 2 := by simp
  
  #check exists_has_deriv_at_eq_slope
  
  #check exists_deriv_eq_slope
  


