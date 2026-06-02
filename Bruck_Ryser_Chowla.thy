(* Title: Bruck_Ryser_Chowla
   Author: Craig Alan Feinstein
*)

theory Bruck_Ryser_Chowla imports
  Fishers_Inequality.Fishers_Inequality SumSquares.FourSquares Pell.Pell 
  Van_der_Waerden.Digits
begin 

section ‹Bruck Ryser Chowla Theorem›
text ‹The Bruck Ryser Chowla Theorem states the following:
Let $(v,k,\Lambda)$ be a symmetric BIBD. If v is even, 
then $k-\Lambda$ will be a perfect square. And if v is odd,
then there will exist integers $(x,y,z) \neq (0,0,0)$ such that
$x^2 = (k-Λ) y^2 = (-1)^{(v-1)/2}Λz^2$. The proof comes from 
"Combinatorial Designs: Constructions and Analysis" by Douglas R.
Stinson.›

context ordered_sym_bibd
begin

subsection ‹v is even›

lemma apply_nec_cond_one_1: shows "𝗄 * (𝗄 - 1) = Λ * (𝗏 - 1)"
proof -
  have "𝗋 = 𝗄" using rep_value_sym by simp
    moreover have "𝗋 * (𝗄 - 1) = Λ * (𝗏 - 1)"
     using necessary_condition_one by simp
      ultimately show "𝗄 * (𝗄 - 1) = Λ * (𝗏 - 1)" by simp
    qed

lemma apply_nec_cond_one_2: shows "𝗄 + Λ * (𝗏 - 1) = 𝗄^2"
proof -
  have "𝗄 + Λ * (𝗏 - 1) = 𝗄 + 𝗄 * (𝗄 - 1)"
    using apply_nec_cond_one_1 by simp
    also have "𝗄 + 𝗄 * (𝗄 - 1) = 𝗄^2"
      by (simp add: algebra_simps power2_eq_square)
    ultimately show "𝗄 + Λ * (𝗏 - 1) = 𝗄^2"
      using apply_nec_cond_one_1 by simp
  qed

lemma apply_nec_cond_one_3: shows
  "(𝗄 + Λ * (𝗏 - 1))* (𝗄 - Λ)^(𝗏 - 1) = 𝗄^2 * (𝗄 - Λ)^(𝗏 - 1)"
proof -
  have "(𝗄 + Λ * (𝗏 - 1))* (𝗄 - Λ)^(𝗏 - 1) = 𝗄^2 * (𝗄 - Λ)^(𝗏 - 1)"
    using apply_nec_cond_one_2 by simp
  thus ?thesis by simp
qed

lemma det_incidence: "(det N)^2 = det (N * N⇧T)"
proof - 
  have "det (N * N⇧T) = det N * det N⇧T" 
  by (metis (full_types) N_carrier_mat det_mult local.symmetric transpose_carrier_mat)
  also have "det N * det N⇧T = det N * det N"
  using N_carrier_mat det_transpose local.symmetric by auto
  then have "det (N * N⇧T) = (det N)^2" by (simp add: calculation power2_eq_square)
  thus ?thesis by simp
qed 

lemma sym_det_in_mat_square:
 "(det N)^2 = 𝗄^2 * (𝗄 - Λ)^(𝗏 - 1)"
proof - 
  have "det (N * N⇧T) = (𝗋 + Λ * (𝗏 - 1))* (𝗋 - Λ)^(𝗏 - 1)"
    using determinant_inc_mat_square by simp
    then have "det (N * N⇧T) = (𝗄 + Λ * (𝗏 - 1))* (𝗄 - Λ)^(𝗏 - 1)"
      using rep_value_sym by simp
    also have "(𝗄 + Λ * (𝗏 - 1))* (𝗄 - Λ)^(𝗏 - 1) = 𝗄^2 * (𝗄 - Λ)^(𝗏 - 1)"
      using apply_nec_cond_one_3 by simp
    then have "det (N * N⇧T) = 𝗄^2 * (𝗄 - Λ)^(𝗏 - 1)" 
      using calculation by argo
    then show ?thesis using det_incidence by simp
  qed

lemma power_of_k_minus_lambda_1:
  "(det N)^2 / 𝗄^2 = (𝗄 - Λ)^(𝗏 - 1)" 
proof - 
  have "(det N)^2 = 𝗄^2 * (𝗄 - Λ)^(𝗏 - 1)" 
    using sym_det_in_mat_square by simp
  then have "(det N)^2 / 𝗄^2 = (𝗄^2 * (𝗄 - Λ)^(𝗏 - 1)) / 𝗄^2" 
    by (simp add: divide_simps)
  also have "... = 𝗄^2 / 𝗄^2 * (𝗄 - Λ)^(𝗏 - 1)" by (simp add: divide_simps)
  also have "... = 1 * (𝗄 - Λ)^(𝗏 - 1)" using rep_not_zero by fastforce
  also have "... = (𝗄 - Λ)^(𝗏 - 1)" by auto
  finally show ?thesis .
  qed

lemma power_of_k_minus_lambda_2: 
  "(det N / 𝗄)^2 = (𝗄 - Λ)^(𝗏 - 1)"
proof -
  have "(det N)^2 / 𝗄^2 = (𝗄 - Λ)^(𝗏 - 1)" 
    using power_of_k_minus_lambda_1 by simp
  then show ?thesis by (simp add: power_divide)
qed

lemma power_of_k_minus_lambda_3: "(sqrt(𝗄 - Λ))^(𝗏 - 1) ∈ ℚ"
proof -
  have "(det N / 𝗄)^2 = (𝗄 - Λ)^(𝗏 - 1)"
    using power_of_k_minus_lambda_2 by simp
  then have "sqrt((𝗄 - Λ)^(𝗏 - 1)) = sqrt((det N / 𝗄)^2)" by auto
  then have "sqrt((𝗄 - Λ)^(𝗏 - 1)) = abs(det N / 𝗄)"
    by (metis real_sqrt_abs)
  also have "(sqrt(𝗄 - Λ))^(𝗏 - 1) = sqrt ((𝗄 - Λ)^(𝗏 - 1))"
      by (simp add: real_sqrt_power) 
  then have "(sqrt(𝗄 - Λ))^(𝗏 - 1) = abs(det N / 𝗄)"
      using calculation by presburger
  also have "abs(det N / 𝗄) ∈ ℚ" by simp
  then show ?thesis by (metis (full_types)
        ‹sqrt (real (𝗄 - Λ)) ^ (𝗏 - 1) = ¦real_of_int (det N) / real 𝗄¦›)
qed

lemma blocksize_gt_index: "𝗄 > Λ"
  using rep_value_sym index_lt_replication by auto

lemma bruck_ryser_chowla_even_rat:
  assumes "even 𝗏"
  shows "sqrt(𝗄 - Λ) ∈ ℚ"
proof -
  have diff_rat: ‹𝗄 - Λ ∈ ℚ› by simp
  have eq: "(sqrt(𝗄 - Λ))^(𝗏 - 1) ∈ ℚ" using power_of_k_minus_lambda_3
    by blast
  from assms obtain m where "𝗏 = 2 * m" "m > 0" using v_non_zero by auto
  then have "𝗏 - 1 = 2 * m - 1" by auto
  then have "(sqrt(𝗄 - Λ))^(2 * m - 1) ∈ ℚ"
    using eq by auto
  then have rat: ‹(sqrt(𝗄 - Λ))^(2 * m) / (sqrt(𝗄 - Λ)) ∈ ℚ›
    using ‹0 < m› div_by_0 div_less_iff_less_mult mult.commute
        nonzero_mult_div_cancel_left one_div_two_eq_zero pos2 power_eq_0_iff
        power_minus_mult zero_less_diff
    by (metis nat_0_less_mult_iff) 
  have eq2: ‹(sqrt(𝗄 - Λ))^(2 * m) / (sqrt(𝗄 - Λ)) = 
    ((𝗄 - Λ))^ m * (1/sqrt(𝗄 - Λ))›
    using blocksize_gt_index
    by (simp add: power_mult)
  moreover have ‹(𝗄 - Λ) ^ m ∈ ℚ›
    using diff_rat by (simp add: power_mult Rats_mult_iff)
  ultimately have ‹1/sqrt(𝗄 - Λ) ∈ ℚ›
    using rat blocksize_gt_index Rats_mult_iff by force
  then show ?thesis
    by (simp add: divide_inverse)
qed

theorem bruck_ryser_chowla_even:
  assumes "even 𝗏"
  shows "sqrt(𝗄 - Λ) ∈ ℕ"
proof -
  have brc_rat: "sqrt(𝗄 - Λ) ∈ ℚ" 
    using bruck_ryser_chowla_even_rat assms by simp
  then show ?thesis using sqrt_nat_or_irrat' by blast  
qed

end

subsection ‹v is odd›

sublocale ordered_bibd ⊆ ordered_regular_pairwise_balance 𝒱s ℬs Λ 𝗋
  by unfold_locales

context ordered_sym_bibd

begin

lemma lambda_all_ones:
  fixes l :: "'b :: {monoid_mult, zero}"
  assumes "h < 𝗏" "j < 𝗏"
  shows "(l ⋅⇩m (J⇩m 𝗏)) $$ (j, h) = l"
  using assms by simp

lemma lambda_all_ones_extension:
  fixes x :: "rat mat"
  shows "(∑j ∈ {0..<𝗏}. ∑h ∈ {0..<𝗏}.
      (of_nat Λ ⋅⇩m J⇩m 𝗏) $$ (j, h) * x $$ (j, 0) * x $$ (h, 0))
   = of_nat Λ * (∑j ∈ {0..<𝗏}. x $$ (j, 0))^2"
proof -
  have J: "(of_nat Λ ⋅⇩m J⇩m 𝗏) $$ (j,h) = of_nat Λ"
    if "j < 𝗏" "h < 𝗏" for j h
    using that by simp
  have "(∑j ∈ {0..<𝗏}. ∑h ∈ {0..<𝗏}. (of_nat Λ ⋅⇩m J⇩m 𝗏) $$ (j, h) * x $$ (j, 0) * x $$ (h, 0))
    = (∑j=0..<𝗏. ∑h=0..<𝗏. of_nat Λ * x$$(j,0) * x$$(h,0))"
    using J by simp
  also have "... = (∑j=0..<𝗏. ∑h=0..<𝗏. of_nat Λ * (x$$(j,0) * x$$(h,0)))"
    by (simp add: algebra_simps)
  also have "… = (∑j ∈ {0..<𝗏}. of_nat Λ * (∑h ∈ {0..<𝗏}. x$$(j,0) * x$$(h,0)))"
    by (simp add: sum_distrib_left)
  also have "… = of_nat Λ * (∑j ∈ {0..<𝗏}. (∑h ∈ {0..<𝗏}. x$$(j,0) * x$$(h,0)))"
    by (simp add: sum_distrib_left)
  also have "… = of_nat Λ * ((∑j ∈ {0..<𝗏}. x$$(j,0)) * (∑h ∈ {0..<𝗏}. x$$(h,0)))"
    by (metis sum_product)
  also have "… = of_nat Λ * (∑j ∈ {0..<𝗏}. x$$(j,0))^2"
    by (metis power2_eq_square)
  finally show ?thesis .
qed

lemma identity_matrix_property:
  fixes x :: "rat mat"
  shows "int (𝗋 - Λ) * (∑ j ∈ {0..<𝗏}. (∑ h ∈ {0..<𝗏}.  
         (if j = h then 1 else 0) * x $$ (h, 0) * x $$ (j, 0))) = 
         int (𝗋 - Λ) * (∑j ∈ {0..<𝗏}. (x $$ (j, 0))^2)"
proof -
  have step1: "⋀j h. (if j = h then 1 else 0) * x $$ (h, 0) * x $$ (j, 0) = 
                     (if j = h then x $$ (h, 0) * x $$ (j, 0) else 0)"
    by auto
  have "int (𝗋 - Λ) * (∑ j ∈ {0..<𝗏}. (∑ h ∈ {0..<𝗏}. (if j = h then 1 else 0) * x $$ (h, 0) * x $$ (j, 0)))
      = int (𝗋 - Λ) * (∑ j ∈ {0..<𝗏}. (∑ h ∈ {0..<𝗏}. (if j = h then x $$ (h, 0) * x $$ (j, 0) else 0)))"
    using step1 by simp
  also have "... = int (𝗋 - Λ) * (∑ j ∈ {0..<𝗏}. x $$ (j, 0) * x $$ (j, 0))"
    by simp
  also have "... = int (𝗋 - Λ) * (∑ j ∈ {0..<𝗏}. (x $$ (j, 0))^2)"
    by (simp add: power2_eq_square)
  finally show ?thesis .
qed

lemma order_times_identity_matrix:
  fixes x :: "rat mat"
  shows
  "(∑ j<𝗏. ∑ h<𝗏.
      (rat_of_nat (𝗋 - Λ) ⋅⇩m 1⇩m 𝗏) $$ (j,h) * x $$ (j,0) * x $$ (h,0))
   = rat_of_nat (𝗋 - Λ) * (∑ j<𝗏. (x $$ (j,0))^2)"
proof -
  have step: "⋀j h. rat_of_nat (𝗋 - Λ) * (if j = h then 1 else 0) * x $$ (j,0) * x $$ (h,0) =
                     (if j = h then rat_of_nat (𝗋 - Λ) * x $$ (j,0) * x $$ (h,0) else 0)"
    by auto
  have "(∑ j<𝗏. ∑ h<𝗏. (rat_of_nat (𝗋 - Λ) ⋅⇩m 1⇩m 𝗏) $$ (j,h) * x $$ (j,0) * x $$ (h,0))
      = (∑ j<𝗏. ∑ h<𝗏. rat_of_nat (𝗋 - Λ) * (if j = h then 1 else 0) * x $$ (j,0) * x $$ (h,0))"
    unfolding one_mat_def by simp
  also have "... = (∑ j<𝗏. ∑ h<𝗏. (if j = h then rat_of_nat (𝗋 - Λ) * x $$ (j,0) * x $$ (h,0) else 0))"
    by (subst step) simp
  also have "... = (∑ j<𝗏. rat_of_nat (𝗋 - Λ) * x $$ (j,0) * x $$ (j,0))"
    by simp
  also have "... = rat_of_nat (𝗋 - Λ) * (∑ j<𝗏. x $$ (j,0) * x $$ (j,0))"
    by (simp add: sum_distrib_left mult.assoc)
  also have "... = rat_of_nat (𝗋 - Λ) * (∑ j<𝗏. (x $$ (j,0))^2)"
    unfolding power2_eq_square by simp
  finally show ?thesis .
qed

lemma combine_r_lambda_terms:
  fixes x :: "rat mat"
  shows "(∑j ∈ {0..<𝗏}. (∑h ∈ {0..<𝗏}. 
    ((of_int (int Λ) ⋅⇩m (J⇩m 𝗏)) $$ (j, h) * x $$ (j, 0) * x $$ (h, 0)))) +
    (∑j ∈ {0..<𝗏}.(∑h ∈ {0..<𝗏}.(of_int (int (𝗋 - Λ)) ⋅⇩m (1⇩m 𝗏)) $$ (j, h) * 
    x $$ (j, 0) * x $$ (h, 0))) = of_int (int Λ) * (∑j ∈ {0..<𝗏}.(x $$ (j, 0)))^2 + 
    of_int (int (𝗋 - Λ)) * (∑j ∈ {0..<𝗏}. (x $$ (j, 0))^2)"
proof -
  have lam: "(∑j ∈{0..<𝗏} .(∑h ∈{0..<𝗏} .(of_int (int Λ) ⋅⇩m (J⇩m 𝗏)) $$ (j, h) * x $$ (j, 0) * x $$ (h, 0))) =
    of_int (int Λ) * (∑j ∈ {0..<𝗏}.(x $$ (j, 0)))^2"
  proof -
    have "(of_int (int Λ) ⋅⇩m (J⇩m 𝗏 :: rat mat)) = (of_nat Λ ⋅⇩m (J⇩m 𝗏 :: rat mat))"
      by simp
    then show ?thesis using lambda_all_ones_extension by fastforce
  qed
  have ord: "(∑j ∈{0..<𝗏} .(∑h ∈{0..<𝗏}.(of_int (int (𝗋 - Λ)) ⋅⇩m (1⇩m 𝗏)) $$ (j, h) * x $$ (j, 0) * x $$ (h, 0))) =
        of_int (int (𝗋 - Λ)) * (∑j ∈ {0..<𝗏}. (x $$ (j, 0))^2)"
  proof -
    have eq: "(of_int (int (𝗋 - Λ)) ⋅⇩m (1⇩m 𝗏 :: rat mat)) = (rat_of_nat (𝗋 - Λ) ⋅⇩m (1⇩m 𝗏 :: rat mat))"
      by simp
    have "(∑j ∈{0..<𝗏} .(∑h ∈{0..<𝗏}.(of_int (int (𝗋 - Λ)) ⋅⇩m (1⇩m 𝗏)) $$ (j, h) * x $$ (j, 0) * x $$ (h, 0))) =
          (∑j ∈{0..<𝗏} .(∑h ∈{0..<𝗏}.(rat_of_nat (𝗋 - Λ) ⋅⇩m (1⇩m 𝗏)) $$ (j, h) * x $$ (j, 0) * x $$ (h, 0)))"
      using eq by metis
    also have "... = rat_of_nat (𝗋 - Λ) * (∑j ∈ {0..<𝗏}. (x $$ (j, 0))^2)"
      using order_times_identity_matrix[of x] by (simp add: atLeast0LessThan)
    also have "... = of_int (int (𝗋 - Λ)) * (∑j ∈ {0..<𝗏}. (x $$ (j, 0))^2)"
      by simp
    finally show ?thesis .
  qed
  show ?thesis using lam ord by simp
qed

lemma brc_x_identity:
  fixes x :: "rat mat"
  shows "(∑j ∈ {0..<𝗏}. (∑h ∈ {0..<𝗏}. (∑i ∈ {0..<𝗏}.  
    of_int (N $$ (j,i)) * of_int (N $$ (h,i))) * x $$ (j,0) * x $$ (h,0))) =
     of_int (int Λ) * (∑j ∈ {0..<𝗏}.(x $$ (j, 0)))^2 +
     of_int (int (𝗋 - Λ)) * (∑j ∈ {0..<𝗏}. (x $$ (j, 0))^2)"
proof -
  have matdef: "(∑i ∈{0..<𝗏} . 
    of_int (N $$ (j,i)) * of_int (N $$ (h,i))) = of_int ((N * N⇧T) $$ (j, h))" 
    if "h < 𝗏" "j < 𝗏" for h j
    using transpose_mat_mult_entries[of "j" "N" "h"]
    local.symmetric that by simp
  have matcond: "of_int ((N * N⇧T) $$ (j, h)) = 
    ((of_int (int Λ) ⋅⇩m (J⇩m 𝗏) + of_int (int (𝗋 - Λ)) ⋅⇩m (1⇩m 𝗏)) $$ (j, h) :: rat)"
    if "h < 𝗏" "j < 𝗏" for h j 
    using rpbd_incidence_matrix_cond that(1) that(2) by simp
  have sum_eq_rLambda: "(∑i ∈ {0..<𝗏}. of_int (N $$ (j,i)) * of_int (N $$ (h,i))) = 
    ((of_int (int Λ) ⋅⇩m (J⇩m 𝗏) + of_int (int (𝗋 - Λ)) ⋅⇩m (1⇩m 𝗏)) $$ (j, h) :: rat)"
    if "h < 𝗏" "j < 𝗏" for h j
  proof -
    have "(∑i ∈{0..<𝗏} . of_int (N $$ (j,i)) * of_int (N $$ (h,i))) = of_int ((N * N⇧T) $$ (j, h))"
      using matdef[OF that] .
    also have "... = ((of_int (int Λ) ⋅⇩m (J⇩m 𝗏) + of_int (int (𝗋 - Λ)) ⋅⇩m (1⇩m 𝗏)) $$ (j, h) :: rat)"
      using matcond[OF that] .
    finally show ?thesis .
  qed
  have "(∑i ∈ {0..<𝗏}. 
    of_int (N $$ (j, i)) * of_int (N $$ (h, i))) * x $$ (j, 0) * x $$ (h, 0) = 
    ((of_int (int Λ) ⋅⇩m (J⇩m 𝗏) + of_int (int (𝗋 - Λ)) ⋅⇩m (1⇩m 𝗏)) $$ (j, h)) * 
    x $$ (j, 0) * x $$ (h, 0)" if "h < 𝗏" "j < 𝗏" for h j
    using sum_eq_rLambda[OF that] by simp
  then have "(∑j ∈ {0..<𝗏}. (∑h ∈ {0..<𝗏}. (∑i ∈ {0..<𝗏}. 
    of_int (N $$ (j, i)) * of_int (N $$ (h, i))) * x $$ (j, 0) * x $$ (h, 0))) = 
    (∑j ∈ {0..<𝗏}. (∑h ∈ {0..<𝗏}. 
    ((of_int (int Λ) ⋅⇩m (J⇩m 𝗏) + of_int (int (𝗋 - Λ)) ⋅⇩m (1⇩m 𝗏)) $$ (j, h)) *
     x $$ (j, 0) * x $$ (h, 0)))" by (intro sum.mono_neutral_cong_right) auto
  also have "... = (∑j ∈ {0..<𝗏}. (∑h ∈ {0..<𝗏}. 
    ((of_int (int Λ) ⋅⇩m (J⇩m 𝗏)) $$ (j, h) * x $$ (j, 0) * x $$ (h, 0)) +
    (of_int (int (𝗋 - Λ)) ⋅⇩m (1⇩m 𝗏)) $$ (j, h) * x $$ (j, 0) * x $$ (h, 0)))"
    by (simp add: algebra_simps sum_distrib_left sum_distrib_right)
  also have "... = (∑j ∈ {0..<𝗏}. (∑h ∈ {0..<𝗏}. 
    ((of_int (int Λ) ⋅⇩m (J⇩m 𝗏)) $$ (j, h) * x $$ (j, 0) * x $$ (h, 0))) +
    (∑h ∈ {0..<𝗏}.(of_int (int (𝗋 - Λ)) ⋅⇩m (1⇩m 𝗏)) $$ (j, h) * 
    x $$ (j, 0) * x $$ (h, 0)))" by (simp add: sum.distrib)
  also have "... = (∑j ∈ {0..<𝗏}. (∑h ∈ {0..<𝗏}. 
    ((of_int (int Λ) ⋅⇩m (J⇩m 𝗏)) $$ (j, h) * x $$ (j, 0) * x $$ (h, 0)))) +
    (∑j ∈ {0..<𝗏}.(∑h ∈ {0..<𝗏}. (of_int (int (𝗋 - Λ)) ⋅⇩m (1⇩m 𝗏)) $$ (j, h) * 
    x $$ (j, 0) * x $$ (h, 0)))" 
    by (simp add: sum.distrib)
  also have final_equ:  "... = of_int (int Λ) * (∑j ∈ {0..<𝗏}.(x $$ (j, 0)))^2 + 
     of_int (int (𝗋 - Λ)) * (∑j ∈ {0..<𝗏}. (x $$ (j, 0))^2)"
    using combine_r_lambda_terms by simp
  finally show ?thesis .
qed

lemma brc_x_equation:
  fixes x :: "rat mat"
  shows "(∑i ∈ {0..<𝗏}.(∑h ∈ {0..<𝗏}. of_int (N $$ (h,i)) * x $$ (h,0))^2) =
     of_int (int Λ) * (∑j ∈ {0..<𝗏}.(x $$ (j, 0)))^2 +
     of_int (int (𝗄 - Λ)) * (∑j ∈ {0..<𝗏}. (x $$ (j, 0))^2)"
proof -
  have r_eq_k: "𝗋 = 𝗄" using rep_value_sym by simp
  have "(∑i ∈ {0..<𝗏}.(∑h ∈ {0..<𝗏}. of_int (N $$ (h,i)) * x $$ (h,0))^2) =
    (∑i ∈ {0..<𝗏}. (∑j ∈ {0..<𝗏}. of_int (N $$ (j, i)) *
    x $$ (j, 0)) * (∑h ∈ {0..<𝗏}. of_int (N $$ (h,i)) * x $$ (h, 0)))"
    by (simp add: power2_eq_square)
  also have "... = (∑i ∈ {0..<𝗏}. (∑j ∈ {0..<𝗏}. (∑h ∈ {0..<𝗏}.
    (of_int (N $$ (j, i)) * x $$ (j,0)) * (of_int (N $$ (h,i)) * x $$ (h,0)))))"
    by (metis (no_types) sum_product)
  also have "... = (∑i ∈ {0..<𝗏}. (∑j ∈ {0..<𝗏}. (∑h ∈ {0..<𝗏}.
    of_int (N $$ (j, i)) * (x $$ (j,0) * of_int (N $$ (h,i))) * x $$ (h,0))))"
    by (simp add: algebra_simps)
  also have "... = (∑i ∈ {0..<𝗏}. (∑j ∈ {0..<𝗏}. (∑h ∈ {0..<𝗏}.
    of_int (N $$ (j, i)) * (of_int (N $$ (h,i)) * x $$ (j,0)) * x $$ (h,0))))"
    by (metis (no_types, lifting) mult_of_int_commute sum.cong)
  also have "... = (∑i ∈ {0..<𝗏}. (∑j ∈ {0..<𝗏}. (∑h ∈ {0..<𝗏}.
    of_int (N $$ (j, i)) * of_int (N $$ (h,i)) * x $$ (j,0) * x $$ (h,0))))"
    by (simp add: algebra_simps)
  also have "... = (∑j ∈ {0..<𝗏}. (∑h ∈ {0..<𝗏}. (∑i ∈ {0..<𝗏}.  
    of_int (N $$ (j, i)) * of_int (N $$ (h,i)) * x $$ (j,0) * x $$ (h,0))))"
    using sum_reorder_triple[of "λ i j h . of_int (N $$ (j, i)) * of_int (N $$ (h,i)) * 
        x $$ (j,0) * x $$ (h,0)" "{0..<𝗏}" "{0..<𝗏}" "{0..<𝗏}"] 
    by blast
  also have "... = (∑j ∈ {0..<𝗏}. (∑h ∈ {0..<𝗏}. (∑i ∈ {0..<𝗏}.  
    of_int (N $$ (j, i)) * of_int (N $$ (h,i))) * x $$ (j,0) * x $$ (h,0)))"
    by (simp add: algebra_simps sum_distrib_left sum_distrib_right)
  also have "... = of_int (int Λ) * (∑j ∈ {0..<𝗏}.(x $$ (j, 0)))^2 +
     of_int (int (𝗋 - Λ)) * (∑j ∈ {0..<𝗏}. (x $$ (j, 0))^2)"
    using brc_x_identity by simp
  also have "... = of_int (int Λ) * (∑j ∈ {0..<𝗏}. (x $$ (j, 0)))^2 +
     of_int (int (𝗄 - Λ)) * (∑j ∈ {0..<𝗏}. (x $$ (j, 0))^2)"
    using r_eq_k by simp
  finally show ?thesis .
qed

fun y_reversible :: "((nat × nat × nat × nat) × (rat × rat × rat × rat)) ⇒ 
             ((nat × nat × nat × nat) × (rat × rat × rat × rat))" where
  "y_reversible((a, b, c, d),(x0, x1, x2, x3)) = ((a, b, c, d),
   ( (of_nat a * x0 + of_nat b * x1 + of_nat c * x2 + of_nat d * x3),
   (- of_nat b * x0 + of_nat a * x1 - of_nat d * x2 + of_nat c * x3),
   (- of_nat c * x0 + of_nat d * x1 + of_nat a * x2 - of_nat b * x3),
   (- of_nat d * x0 - of_nat c * x1 + of_nat b * x2 + of_nat a * x3)))"

fun y_of :: "((nat × nat × nat × nat) × (rat × rat × rat × rat)) ⇒ 
                  (rat × rat × rat × rat)" where
  "y_of((a, b, c, d),(x0, x1, x2, x3)) = snd(y_reversible((a, b, c, d),(x0, x1, x2, x3)))"

fun y_inv_reversible ::"((nat × nat × nat × nat) × (rat × rat × rat × rat)) ⇒ 
             ((nat × nat × nat × nat) × (rat × rat × rat × rat))" where
  "y_inv_reversible((a, b, c, d),(y0, y1, y2, y3)) = ((a, b, c, d),
  ((of_nat a)*y0 - (of_nat b)*y1 - (of_nat c)*y2 - (of_nat d)*y3)/of_nat(a^2 + b^2 + c^2 + d^2), 
  ((of_nat b)*y0 + (of_nat a)*y1 + (of_nat d)*y2 - (of_nat c)*y3)/of_nat(a^2 + b^2 + c^2 + d^2),
  ((of_nat c)*y0 + (of_nat a)*y2 + (of_nat b)*y3 - (of_nat d)*y1)/of_nat(a^2 + b^2 + c^2 + d^2),
  ((of_nat d)*y0 + (of_nat c)*y1 + (of_nat a)*y3 - (of_nat b)*y2)/of_nat(a^2 + b^2 + c^2 + d^2))"

fun y_inv_of :: "((nat × nat × nat × nat) × (rat × rat × rat × rat)) ⇒ 
                  (rat × rat × rat × rat)" where
  "y_inv_of((a, b, c, d),(y0, y1, y2, y3)) = 
   snd(y_inv_reversible((a, b, c, d),(y0, y1, y2, y3)))"

fun one_of :: "(rat × rat × rat × rat) ⇒ rat" where
  "one_of(y0, y1, y2, y3) = y0"

fun two_of :: "(rat × rat × rat × rat) ⇒ rat" where
  "two_of(y0, y1, y2, y3) = y1"

fun three_of :: "(rat × rat × rat × rat) ⇒ rat" where
  "three_of(y0, y1, y2, y3) = y2"

fun four_of :: "(rat × rat × rat × rat) ⇒ rat" where
  "four_of(y0, y1, y2, y3) = y3"

lemma y_inverses_part_1:
  fixes a :: "nat"
  fixes b :: "nat"
  fixes c :: "nat"
  fixes d :: "nat"
  fixes x0 :: "rat"
  fixes x1 :: "rat"
  fixes x2 :: "rat"
  fixes x3 :: "rat"
  assumes "a^2 + b^2 + c^2 + d^2 ≠ 0"
  shows "y_inv_reversible(y_reversible((a, b, c, d),(x0, x1, x2, x3))) = 
         ((a, b, c, d),(x0, x1, x2, x3))"
proof - 
  have "y_reversible((a, b, c, d),(x0, x1, x2, x3)) = ((a, b, c, d),
   ( (of_nat a * x0 + of_nat b * x1 + of_nat c * x2 + of_nat d * x3),
   (- of_nat b * x0 + of_nat a * x1 - of_nat d * x2 + of_nat c * x3),
   (- of_nat c * x0 + of_nat d * x1 + of_nat a * x2 - of_nat b * x3),
   (- of_nat d * x0 - of_nat c * x1 + of_nat b * x2 + of_nat a * x3)))" by simp
  then have "y_inv_reversible(y_reversible((a, b, c, d),(x0, x1, x2, x3))) = 
   y_inv_reversible((a, b, c, d),
   ( (of_nat a * x0 + of_nat b * x1 + of_nat c * x2 + of_nat d * x3),
   (- of_nat b * x0 + of_nat a * x1 - of_nat d * x2 + of_nat c * x3),
   (- of_nat c * x0 + of_nat d * x1 + of_nat a * x2 - of_nat b * x3),
   (- of_nat d * x0 - of_nat c * x1 + of_nat b * x2 + of_nat a * x3)))" by simp
  then have key: "y_inv_reversible(y_reversible((a, b, c, d),(x0, x1, x2, x3))) = 
   ((a, b, c, d),
   ((of_nat a * (of_nat a * x0 + of_nat b * x1 + of_nat c * x2 + of_nat d * x3) - 
    of_nat b * (- of_nat b * x0 + of_nat a * x1 - of_nat d * x2 + of_nat c * x3) - 
    of_nat c * (- of_nat c * x0 + of_nat d * x1 + of_nat a * x2 - of_nat b * x3) - 
    of_nat d * (- of_nat d * x0 - of_nat c * x1 + of_nat b * x2 + of_nat a * x3))/
    of_nat(a^2 + b^2 + c^2 + d^2),
    (of_nat b * (of_nat a * x0 + of_nat b * x1 + of_nat c * x2 + of_nat d * x3) + 
    of_nat a * (- of_nat b * x0 + of_nat a * x1 - of_nat d * x2 + of_nat c * x3) + 
    of_nat d * (- of_nat c * x0 + of_nat d * x1 + of_nat a * x2 - of_nat b * x3) - 
    of_nat c * (- of_nat d * x0 - of_nat c * x1 + of_nat b * x2 + of_nat a * x3))/
    of_nat(a^2 + b^2 + c^2 + d^2),
    (of_nat c * (of_nat a * x0 + of_nat b * x1 + of_nat c * x2 + of_nat d * x3) -
    of_nat d * (- of_nat b * x0 + of_nat a * x1 - of_nat d * x2 + of_nat c * x3) +
    of_nat a * (- of_nat c * x0 + of_nat d * x1 + of_nat a * x2 - of_nat b * x3) +
    of_nat b * (- of_nat d * x0 - of_nat c * x1 + of_nat b * x2 + of_nat a * x3))/
    of_nat(a^2 + b^2 + c^2 + d^2),
    (of_nat d * (of_nat a * x0 + of_nat b * x1 + of_nat c * x2 + of_nat d * x3) +
    of_nat c * (- of_nat b * x0 + of_nat a * x1 - of_nat d * x2 + of_nat c * x3) -
    of_nat b * (- of_nat c * x0 + of_nat d * x1 + of_nat a * x2 - of_nat b * x3) +
    of_nat a * (- of_nat d * x0 - of_nat c * x1 + of_nat b * x2 + of_nat a * x3))/
    of_nat(a^2 + b^2 + c^2 + d^2)))"
    by simp

  have "of_nat a * (of_nat a * x0 + of_nat b * x1 + of_nat c * x2 + of_nat d * x3) -
     of_nat b * (- of_nat b * x0 + of_nat a * x1 - of_nat d * x2 + of_nat c * x3) -
     of_nat c * (- of_nat c * x0 + of_nat d * x1 + of_nat a * x2 - of_nat b * x3) -
     of_nat d * (- of_nat d * x0 - of_nat c * x1 + of_nat b * x2 + of_nat a * x3) = 
    of_nat(a^2 + b^2 + c^2 + d^2) * x0"
    by (simp add: power2_eq_square algebra_simps)

  then have
     "(of_nat a * (of_nat a * x0 + of_nat b * x1 + of_nat c * x2 + of_nat d * x3) -
     of_nat b * (- of_nat b * x0 + of_nat a * x1 - of_nat d * x2 + of_nat c * x3) -
     of_nat c * (- of_nat c * x0 + of_nat d * x1 + of_nat a * x2 - of_nat b * x3) -
     of_nat d * (- of_nat d * x0 - of_nat c * x1 + of_nat b * x2 + of_nat a * x3)) / 
    of_nat(a^2 + b^2 + c^2 + d^2) = x0 * of_nat(a^2 + b^2 + c^2 + d^2)/ 
    of_nat(a^2 + b^2 + c^2 + d^2)"
    using assms by (simp add: algebra_simps)

  then have first_component_simplified: 
     "(of_nat a * (of_nat a * x0 + of_nat b * x1 + of_nat c * x2 + of_nat d * x3) -
     of_nat b * (- of_nat b * x0 + of_nat a * x1 - of_nat d * x2 + of_nat c * x3) -
     of_nat c * (- of_nat c * x0 + of_nat d * x1 + of_nat a * x2 - of_nat b * x3) -
     of_nat d * (- of_nat d * x0 - of_nat c * x1 + of_nat b * x2 + of_nat a * x3)) / 
    of_nat(a^2 + b^2 + c^2 + d^2) = x0"
    using assms by (metis nonzero_eq_divide_eq of_nat_0_eq_iff)

  have "of_nat b * (of_nat a * x0 + of_nat b * x1 + of_nat c * x2 + of_nat d * x3) +
     of_nat a * (- of_nat b * x0 + of_nat a * x1 - of_nat d * x2 + of_nat c * x3) +
     of_nat d * (- of_nat c * x0 + of_nat d * x1 + of_nat a * x2 - of_nat b * x3) -
     of_nat c * (- of_nat d * x0 - of_nat c * x1 + of_nat b * x2 + of_nat a * x3) = 
    of_nat(a^2 + b^2 + c^2 + d^2) *x1"
    by (simp add: power2_eq_square algebra_simps)

  then have
    "(of_nat b * (of_nat a * x0 + of_nat b * x1 + of_nat c * x2 + of_nat d * x3) +
     of_nat a * (- of_nat b * x0 + of_nat a * x1 - of_nat d * x2 + of_nat c * x3) +
     of_nat d * (- of_nat c * x0 + of_nat d * x1 + of_nat a * x2 - of_nat b * x3) -
     of_nat c * (- of_nat d * x0 - of_nat c * x1 + of_nat b * x2 + of_nat a * x3)) / 
     of_nat(a^2 + b^2 + c^2 + d^2) = x1 * of_nat(a^2 + b^2 + c^2 + d^2)/ 
     of_nat(a^2 + b^2 + c^2 + d^2)"
    using assms by (simp add: algebra_simps)

  then have second_component_simplified:
    "(of_nat b * (of_nat a * x0 + of_nat b * x1 + of_nat c * x2 + of_nat d * x3) +
     of_nat a * (- of_nat b * x0 + of_nat a * x1 - of_nat d * x2 + of_nat c * x3) +
     of_nat d * (- of_nat c * x0 + of_nat d * x1 + of_nat a * x2 - of_nat b * x3) -
     of_nat c * (- of_nat d * x0 - of_nat c * x1 + of_nat b * x2 + of_nat a * x3)) / 
     of_nat(a^2 + b^2 + c^2 + d^2) = x1"
    using assms by (metis nonzero_eq_divide_eq of_nat_0_eq_iff)

  have "of_nat c * (of_nat a * x0 + of_nat b * x1 + of_nat c * x2 + of_nat d * x3) -
     of_nat d * (- of_nat b * x0 + of_nat a * x1 - of_nat d * x2 + of_nat c * x3) +
     of_nat a * (- of_nat c * x0 + of_nat d * x1 + of_nat a * x2 - of_nat b * x3) +
     of_nat b * (- of_nat d * x0 - of_nat c * x1 + of_nat b * x2 + of_nat a * x3) = 
     of_nat(a^2 + b^2 + c^2 + d^2) * x2"
    by (simp add: power2_eq_square algebra_simps)

  then have 
    "(of_nat c * (of_nat a * x0 + of_nat b * x1 + of_nat c * x2 + of_nat d * x3) -
     of_nat d * (- of_nat b * x0 + of_nat a * x1 - of_nat d * x2 + of_nat c * x3) +
     of_nat a * (- of_nat c * x0 + of_nat d * x1 + of_nat a * x2 - of_nat b * x3) +
     of_nat b * (- of_nat d * x0 - of_nat c * x1 + of_nat b * x2 + of_nat a * x3)) / 
     of_nat(a^2 + b^2 + c^2 + d^2) = x2 * of_nat(a^2 + b^2 + c^2 + d^2)/ 
     of_nat(a^2 + b^2 + c^2 + d^2)"
    using assms by (simp add: algebra_simps)

  then have third_component_simplified:
    "(of_nat c * (of_nat a * x0 + of_nat b * x1 + of_nat c * x2 + of_nat d * x3) -
     of_nat d * (- of_nat b * x0 + of_nat a * x1 - of_nat d * x2 + of_nat c * x3) +
     of_nat a * (- of_nat c * x0 + of_nat d * x1 + of_nat a * x2 - of_nat b * x3) +
     of_nat b * (- of_nat d * x0 - of_nat c * x1 + of_nat b * x2 + of_nat a * x3)) / 
     of_nat(a^2 + b^2 + c^2 + d^2) = x2"
    using assms by (metis nonzero_eq_divide_eq of_nat_0_eq_iff)

  have "of_nat d * (of_nat a * x0 + of_nat b * x1 + of_nat c * x2 + of_nat d * x3) +
     of_nat c * (- of_nat b * x0 + of_nat a * x1 - of_nat d * x2 + of_nat c * x3) -
     of_nat b * (- of_nat c * x0 + of_nat d * x1 + of_nat a * x2 - of_nat b * x3) +
     of_nat a * (- of_nat d * x0 - of_nat c * x1 + of_nat b * x2 + of_nat a * x3) = 
     of_nat(a^2 + b^2 + c^2 + d^2) * x3"
    by (simp add: power2_eq_square algebra_simps)

  then have 
    "(of_nat d * (of_nat a * x0 + of_nat b * x1 + of_nat c * x2 + of_nat d * x3) +
     of_nat c * (- of_nat b * x0 + of_nat a * x1 - of_nat d * x2 + of_nat c * x3) -
     of_nat b * (- of_nat c * x0 + of_nat d * x1 + of_nat a * x2 - of_nat b * x3) +
     of_nat a * (- of_nat d * x0 - of_nat c * x1 + of_nat b * x2 + of_nat a * x3)) / 
     of_nat(a^2 + b^2 + c^2 + d^2) = x3 * of_nat(a^2 + b^2 + c^2 + d^2)/ 
     of_nat(a^2 + b^2 + c^2 + d^2)"
    using assms by (simp add: algebra_simps)

  then have fourth_component_simplified:
    "(of_nat d * (of_nat a * x0 + of_nat b * x1 + of_nat c * x2 + of_nat d * x3) +
     of_nat c * (- of_nat b * x0 + of_nat a * x1 - of_nat d * x2 + of_nat c * x3) -
     of_nat b * (- of_nat c * x0 + of_nat d * x1 + of_nat a * x2 - of_nat b * x3) +
     of_nat a * (- of_nat d * x0 - of_nat c * x1 + of_nat b * x2 + of_nat a * x3)) / 
     of_nat(a^2 + b^2 + c^2 + d^2) = x3"
   using assms by (metis nonzero_eq_divide_eq of_nat_0_eq_iff)

  then have "y_inv_reversible(y_reversible((a, b, c, d),(x0, x1, x2, x3))) = 
         ((a, b, c, d),(x0, x1, x2, x3))"
  using first_component_simplified second_component_simplified 
       third_component_simplified fourth_component_simplified key by simp
  thus ?thesis 
    by simp
qed

lemma y_inverses_part_2:
  fixes a :: "nat"
  fixes b :: "nat"
  fixes c :: "nat"
  fixes d :: "nat"
  fixes y0 :: "rat"
  fixes y1 :: "rat"
  fixes y2 :: "rat"
  fixes y3 :: "rat"
  assumes "a^2 + b^2 + c^2 + d^2 ≠ 0"
  shows "y_reversible(y_inv_reversible((a, b, c, d),(y0, y1, y2, y3))) = 
         ((a, b, c, d),(y0, y1, y2, y3))"
proof - 
  have "y_inv_reversible((a, b, c, d),(y0, y1, y2, y3)) = ((a, b, c, d),
   ((of_nat a)*y0 - (of_nat b)*y1 - (of_nat c)*y2 - (of_nat d)*y3)/of_nat(a^2 + b^2 + c^2 + d^2), 
   ((of_nat b)*y0 + (of_nat a)*y1 + (of_nat d)*y2 - (of_nat c)*y3)/of_nat(a^2 + b^2 + c^2 + d^2),
   ((of_nat c)*y0 + (of_nat a)*y2 + (of_nat b)*y3 - (of_nat d)*y1)/of_nat(a^2 + b^2 + c^2 + d^2),
   ((of_nat d)*y0 + (of_nat c)*y1 + (of_nat a)*y3 - (of_nat b)*y2)/of_nat(a^2 + b^2 + c^2 + d^2))" 
      by simp
  then have "y_reversible(y_inv_reversible((a, b, c, d),(y0, y1, y2, y3))) = 
   y_reversible((a, b, c, d),
   ((of_nat a)*y0 - (of_nat b)*y1 - (of_nat c)*y2 - (of_nat d)*y3)/of_nat(a^2 + b^2 + c^2 + d^2), 
   ((of_nat b)*y0 + (of_nat a)*y1 + (of_nat d)*y2 - (of_nat c)*y3)/of_nat(a^2 + b^2 + c^2 + d^2),
   ((of_nat c)*y0 + (of_nat a)*y2 + (of_nat b)*y3 - (of_nat d)*y1)/of_nat(a^2 + b^2 + c^2 + d^2),
   ((of_nat d)*y0 + (of_nat c)*y1 + (of_nat a)*y3 - (of_nat b)*y2)/of_nat(a^2 + b^2 + c^2 + d^2))" 
    by simp
  then have key: "y_reversible(y_inv_reversible((a, b, c, d),(y0, y1, y2, y3))) = 
   ((a, b, c, d),
   (of_nat a * ((of_nat a)*y0 - (of_nat b)*y1 - (of_nat c)*y2 - (of_nat d)*y3)/
    of_nat(a^2 + b^2 + c^2 + d^2) + 
    of_nat b * ((of_nat b)*y0 + (of_nat a)*y1 + (of_nat d)*y2 - (of_nat c)*y3)/
    of_nat(a^2 + b^2 + c^2 + d^2) + 
    of_nat c * ((of_nat c)*y0 + (of_nat a)*y2 + (of_nat b)*y3 - (of_nat d)*y1)/
    of_nat(a^2 + b^2 + c^2 + d^2) + 
    of_nat d * ((of_nat d)*y0 + (of_nat c)*y1 + (of_nat a)*y3 - (of_nat b)*y2)/
    of_nat(a^2 + b^2 + c^2 + d^2),
    -of_nat b * ((of_nat a)*y0 - (of_nat b)*y1 - (of_nat c)*y2 - (of_nat d)*y3)/
    of_nat(a^2 + b^2 + c^2 + d^2) + 
    of_nat a * ((of_nat b)*y0 + (of_nat a)*y1 + (of_nat d)*y2 - (of_nat c)*y3)/
    of_nat(a^2 + b^2 + c^2 + d^2) - 
    of_nat d * ((of_nat c)*y0 + (of_nat a)*y2 + (of_nat b)*y3 - (of_nat d)*y1)/
    of_nat(a^2 + b^2 + c^2 + d^2) + 
    of_nat c * ((of_nat d)*y0 + (of_nat c)*y1 + (of_nat a)*y3 - (of_nat b)*y2)/
    of_nat(a^2 + b^2 + c^2 + d^2),
    -of_nat c * ((of_nat a)*y0 - (of_nat b)*y1 - (of_nat c)*y2 - (of_nat d)*y3)/
    of_nat(a^2 + b^2 + c^2 + d^2) +
    of_nat d * ((of_nat b)*y0 + (of_nat a)*y1 + (of_nat d)*y2 - (of_nat c)*y3)/
    of_nat(a^2 + b^2 + c^2 + d^2) +
    of_nat a * ((of_nat c)*y0 + (of_nat a)*y2 + (of_nat b)*y3 - (of_nat d)*y1)/
    of_nat(a^2 + b^2 + c^2 + d^2) -
    of_nat b * ((of_nat d)*y0 + (of_nat c)*y1 + (of_nat a)*y3 - (of_nat b)*y2)/
    of_nat(a^2 + b^2 + c^2 + d^2),
    -of_nat d * ((of_nat a)*y0 - (of_nat b)*y1 - (of_nat c)*y2 - (of_nat d)*y3)/
    of_nat(a^2 + b^2 + c^2 + d^2) -
    of_nat c * ((of_nat b)*y0 + (of_nat a)*y1 + (of_nat d)*y2 - (of_nat c)*y3)/
    of_nat(a^2 + b^2 + c^2 + d^2) +
    of_nat b * ((of_nat c)*y0 + (of_nat a)*y2 + (of_nat b)*y3 - (of_nat d)*y1)/
    of_nat(a^2 + b^2 + c^2 + d^2) +
    of_nat a * ((of_nat d)*y0 + (of_nat c)*y1 + (of_nat a)*y3 - (of_nat b)*y2)/
    of_nat(a^2 + b^2 + c^2 + d^2)))"
    by auto

  have "of_nat a * ((of_nat a)*y0 - (of_nat b)*y1 - (of_nat c)*y2 - (of_nat d)*y3) +
     of_nat b * ((of_nat b)*y0 + (of_nat a)*y1 + (of_nat d)*y2 - (of_nat c)*y3) +
     of_nat c * ((of_nat c)*y0 + (of_nat a)*y2 + (of_nat b)*y3 - (of_nat d)*y1) +
     of_nat d * ((of_nat d)*y0 + (of_nat c)*y1 + (of_nat a)*y3 - (of_nat b)*y2) = 
    of_nat(a^2 + b^2 + c^2 + d^2) * y0"
    by (simp add: power2_eq_square algebra_simps)

  then have
     "(of_nat a * ((of_nat a)*y0 - (of_nat b)*y1 - (of_nat c)*y2 - (of_nat d)*y3) +
     of_nat b * ((of_nat b)*y0 + (of_nat a)*y1 + (of_nat d)*y2 - (of_nat c)*y3) +
     of_nat c * ((of_nat c)*y0 + (of_nat a)*y2 + (of_nat b)*y3 - (of_nat d)*y1) +
     of_nat d * ((of_nat d)*y0 + (of_nat c)*y1 + (of_nat a)*y3 - (of_nat b)*y2)) / 
     of_nat(a^2 + b^2 + c^2 + d^2) = y0 * of_nat(a^2 + b^2 + c^2 + d^2)/ 
     of_nat(a^2 + b^2 + c^2 + d^2)"
    using assms by (simp add: algebra_simps)

  then have first_component_simplified: 
     "of_nat a * ((of_nat a)*y0 - (of_nat b)*y1 - (of_nat c)*y2 - (of_nat d)*y3) / 
     of_nat(a^2 + b^2 + c^2 + d^2) +
     of_nat b * ((of_nat b)*y0 + (of_nat a)*y1 + (of_nat d)*y2 - (of_nat c)*y3) / 
     of_nat(a^2 + b^2 + c^2 + d^2) +
     of_nat c * ((of_nat c)*y0 + (of_nat a)*y2 + (of_nat b)*y3 - (of_nat d)*y1) / 
     of_nat(a^2 + b^2 + c^2 + d^2) +
     of_nat d * ((of_nat d)*y0 + (of_nat c)*y1 + (of_nat a)*y3 - (of_nat b)*y2) / 
    of_nat(a^2 + b^2 + c^2 + d^2) = y0"
   using assms by (smt (verit, best) add_divide_distrib diff_divide_distrib
      nonzero_eq_divide_eq of_nat_0 of_nat_0_eq_iff)

  have "-of_nat b * ((of_nat a)*y0 - (of_nat b)*y1 - (of_nat c)*y2 - (of_nat d)*y3) +
     of_nat a * ((of_nat b)*y0 + (of_nat a)*y1 + (of_nat d)*y2 - (of_nat c)*y3) -
     of_nat d * ((of_nat c)*y0 + (of_nat a)*y2 + (of_nat b)*y3 - (of_nat d)*y1) +
     of_nat c * ((of_nat d)*y0 + (of_nat c)*y1 + (of_nat a)*y3 - (of_nat b)*y2) = 
    of_nat(a^2 + b^2 + c^2 + d^2) *y1"
    by (simp add: power2_eq_square algebra_simps)

  then have
    "(-of_nat b * ((of_nat a)*y0 - (of_nat b)*y1 - (of_nat c)*y2 - (of_nat d)*y3) +
     of_nat a * ((of_nat b)*y0 + (of_nat a)*y1 + (of_nat d)*y2 - (of_nat c)*y3) -
     of_nat d * ((of_nat c)*y0 + (of_nat a)*y2 + (of_nat b)*y3 - (of_nat d)*y1) +
     of_nat c * ((of_nat d)*y0 + (of_nat c)*y1 + (of_nat a)*y3 - (of_nat b)*y2)) / 
     of_nat(a^2 + b^2 + c^2 + d^2) = y1 * of_nat(a^2 + b^2 + c^2 + d^2)/ 
     of_nat(a^2 + b^2 + c^2 + d^2)"
    using assms by (simp add: algebra_simps)

  then have second_component_simplified:
    "-of_nat b * ((of_nat a)*y0 - (of_nat b)*y1 - (of_nat c)*y2 - (of_nat d)*y3) / 
     of_nat(a^2 + b^2 + c^2 + d^2) +
     of_nat a * ((of_nat b)*y0 + (of_nat a)*y1 + (of_nat d)*y2 - (of_nat c)*y3) / 
     of_nat(a^2 + b^2 + c^2 + d^2) -
     of_nat d * ((of_nat c)*y0 + (of_nat a)*y2 + (of_nat b)*y3 - (of_nat d)*y1) / 
     of_nat(a^2 + b^2 + c^2 + d^2) +
     of_nat c * ((of_nat d)*y0 + (of_nat c)*y1 + (of_nat a)*y3 - (of_nat b)*y2) / 
     of_nat(a^2 + b^2 + c^2 + d^2) = y1"
   using assms by (smt (verit, best) add_divide_distrib diff_divide_distrib
      nonzero_eq_divide_eq of_nat_0 of_nat_0_eq_iff)

  have "-of_nat c * ((of_nat a)*y0 - (of_nat b)*y1 - (of_nat c)*y2 - (of_nat d)*y3) + 
     of_nat d * ((of_nat b)*y0 + (of_nat a)*y1 + (of_nat d)*y2 - (of_nat c)*y3) +
     of_nat a * ((of_nat c)*y0 + (of_nat a)*y2 + (of_nat b)*y3 - (of_nat d)*y1) -
     of_nat b * ((of_nat d)*y0 + (of_nat c)*y1 + (of_nat a)*y3 - (of_nat b)*y2) = 
     of_nat(a^2 + b^2 + c^2 + d^2) * y2"
    by (simp add: power2_eq_square algebra_simps)

  then have 
    "(-of_nat c * ((of_nat a)*y0 - (of_nat b)*y1 - (of_nat c)*y2 - (of_nat d)*y3) +
     of_nat d * ((of_nat b)*y0 + (of_nat a)*y1 + (of_nat d)*y2 - (of_nat c)*y3) +
     of_nat a * ((of_nat c)*y0 + (of_nat a)*y2 + (of_nat b)*y3 - (of_nat d)*y1) -
     of_nat b * ((of_nat d)*y0 + (of_nat c)*y1 + (of_nat a)*y3 - (of_nat b)*y2)) / 
     of_nat(a^2 + b^2 + c^2 + d^2) = y2 * of_nat(a^2 + b^2 + c^2 + d^2)/ 
     of_nat(a^2 + b^2 + c^2 + d^2)"
    using assms by (simp add: algebra_simps)

  then have third_component_simplified:
    "-of_nat c * ((of_nat a)*y0 - (of_nat b)*y1 - (of_nat c)*y2 - (of_nat d)*y3) / 
     of_nat(a^2 + b^2 + c^2 + d^2) +
     of_nat d * ((of_nat b)*y0 + (of_nat a)*y1 + (of_nat d)*y2 - (of_nat c)*y3) / 
     of_nat(a^2 + b^2 + c^2 + d^2) +
     of_nat a * ((of_nat c)*y0 + (of_nat a)*y2 + (of_nat b)*y3 - (of_nat d)*y1) / 
     of_nat(a^2 + b^2 + c^2 + d^2) -
     of_nat b * ((of_nat d)*y0 + (of_nat c)*y1 + (of_nat a)*y3 - (of_nat b)*y2) / 
     of_nat(a^2 + b^2 + c^2 + d^2) = y2"
   using assms by (smt (verit, best) add_divide_distrib diff_divide_distrib
      nonzero_eq_divide_eq of_nat_0 of_nat_0_eq_iff)

  have "-of_nat d * ((of_nat a)*y0 - (of_nat b)*y1 - (of_nat c)*y2 - (of_nat d)*y3) -
     of_nat c * ((of_nat b)*y0 + (of_nat a)*y1 + (of_nat d)*y2 - (of_nat c)*y3) +
     of_nat b * ((of_nat c)*y0 + (of_nat a)*y2 + (of_nat b)*y3 - (of_nat d)*y1) +
     of_nat a * ((of_nat d)*y0 + (of_nat c)*y1 + (of_nat a)*y3 - (of_nat b)*y2) = 
     of_nat(a^2 + b^2 + c^2 + d^2) * y3"
    by (simp add: power2_eq_square algebra_simps)

  then have 
    "(-of_nat d * ((of_nat a)*y0 - (of_nat b)*y1 - (of_nat c)*y2 - (of_nat d)*y3) -
     of_nat c * ((of_nat b)*y0 + (of_nat a)*y1 + (of_nat d)*y2 - (of_nat c)*y3) +
     of_nat b * ((of_nat c)*y0 + (of_nat a)*y2 + (of_nat b)*y3 - (of_nat d)*y1) +
     of_nat a * ((of_nat d)*y0 + (of_nat c)*y1 + (of_nat a)*y3 - (of_nat b)*y2)) / 
     of_nat(a^2 + b^2 + c^2 + d^2) = y3 * of_nat(a^2 + b^2 + c^2 + d^2)/ 
     of_nat(a^2 + b^2 + c^2 + d^2)"
    using assms by (simp add: algebra_simps)

  then have fourth_component_simplified:
    "-of_nat d * ((of_nat a)*y0 - (of_nat b)*y1 - (of_nat c)*y2 - (of_nat d)*y3) / 
     of_nat(a^2 + b^2 + c^2 + d^2) -
     of_nat c * ((of_nat b)*y0 + (of_nat a)*y1 + (of_nat d)*y2 - (of_nat c)*y3) / 
     of_nat(a^2 + b^2 + c^2 + d^2) +
     of_nat b * ((of_nat c)*y0 + (of_nat a)*y2 + (of_nat b)*y3 - (of_nat d)*y1) / 
     of_nat(a^2 + b^2 + c^2 + d^2) +
     of_nat a * ((of_nat d)*y0 + (of_nat c)*y1 + (of_nat a)*y3 - (of_nat b)*y2) / 
     of_nat(a^2 + b^2 + c^2 + d^2) = y3"
   using assms by (smt (verit, best) add_divide_distrib diff_divide_distrib
      nonzero_eq_divide_eq of_nat_0 of_nat_0_eq_iff)

  then have "y_reversible(y_inv_reversible((a, b, c, d),(y0, y1, y2, y3))) = 
         ((a, b, c, d),(y0, y1, y2, y3))"
  using first_component_simplified second_component_simplified 
       third_component_simplified fourth_component_simplified key by auto
  thus ?thesis 
    by simp
qed

lemma lagrange_trans_of_4_identity:
  fixes a :: "nat"
  fixes b :: "nat"
  fixes c :: "nat"
  fixes d :: "nat"
  fixes x0 :: "rat"
  fixes x1 :: "rat"
  fixes x2 :: "rat"
  fixes x3 :: "rat"
  shows "one_of(y_of((a, b, c, d),(x0, x1, x2, x3)))^2 +
         two_of(y_of((a, b, c, d), (x0, x1, x2, x3)))^2 +
         three_of(y_of((a, b, c, d), (x0, x1, x2, x3)))^2 +
         four_of(y_of((a, b, c, d), (x0, x1, x2, x3)))^2 = 
         of_nat (a^2 + b^2 + c^2 + d^2)*(x0^2 + x1^2 + x2^2 + x3^2)"
proof -
  have "one_of(y_of((a, b, c, d),(x0, x1, x2, x3)))^2 +
        two_of(y_of((a, b, c, d), (x0, x1, x2, x3)))^2 +
        three_of(y_of((a, b, c, d), (x0, x1, x2, x3)))^2 +
        four_of(y_of((a, b, c, d), (x0, x1, x2, x3)))^2 = 
    ((of_nat a)*x0 + (of_nat b)*x1 + (of_nat c)*x2 + (of_nat d)*x3)^2 +
    (-(of_nat b)*x0 + (of_nat a)*x1 - (of_nat d)*x2 + (of_nat c)*x3)^2 +
    (-(of_nat c)*x0 + (of_nat d)*x1 + (of_nat a)*x2 - (of_nat b)*x3)^2 +
    (-(of_nat d)*x0  -(of_nat c)*x1 + (of_nat b)*x2 + (of_nat a)*x3)^2" by auto

  have eq1: "((of_nat a)*x0 + (of_nat b)*x1 + (of_nat c)*x2 + (of_nat d)*x3)^2 = 
        (of_nat a^2)*x0^2 + (of_nat b^2)*x1^2 + (of_nat c^2)*x2^2 + (of_nat d^2)*x3^2 +
        2*(of_nat a)*(of_nat b)*x0*x1 + 2*(of_nat a)*(of_nat c)*x0*x2 + 
        2*(of_nat a)*(of_nat d)*x0*x3 + 2*(of_nat b)*(of_nat c)*x1*x2 + 
        2*(of_nat b)*(of_nat d)*x1*x3 + 2*(of_nat c)*(of_nat d)*x2*x3"
    by (simp add: power2_eq_square algebra_simps)

  have eq2: "(-(of_nat b)*x0 + (of_nat a)*x1 - (of_nat d)*x2 + (of_nat c)*x3)^2 = 
        (of_nat a^2)*x1^2 + (of_nat b^2)*x0^2 + (of_nat c^2)*x3^2 + 
        (of_nat d^2)*x2^2 - 2*(of_nat a)*(of_nat b)*x0*x1 + 
        2*(of_nat a)*(of_nat c)*x1*x3 - 2*(of_nat a)*(of_nat d)*x1*x2 - 
        2*(of_nat b)*(of_nat c)*x0*x3 + 2*(of_nat b)*(of_nat d)*x0*x2 - 
        2*(of_nat c)*(of_nat d)*x2*x3"
    by (simp add: power2_eq_square algebra_simps)

  have eq3: "(-(of_nat c)*x0 + (of_nat d)*x1 + (of_nat a)*x2 - (of_nat b)*x3)^2 = 
       (of_nat a^2)*x2^2 + (of_nat b^2)*x3^2 + (of_nat c^2)*x0^2 + (of_nat d^2)*x1^2 - 
       2*(of_nat a)*(of_nat b)*x2*x3 - 2*(of_nat a)*(of_nat c)*x0*x2 + 
       2*(of_nat a)*(of_nat d)*x1*x2 + 2*(of_nat b)*(of_nat c)*x0*x3 - 
       2*(of_nat b)*(of_nat d)*x1*x3 - 2*(of_nat c)*(of_nat d)*x0*x1"
    by (simp add: power2_eq_square algebra_simps)

  have eq4: "(-(of_nat d)*x0 - (of_nat c)*x1 + (of_nat b)*x2 + (of_nat a)*x3)^2 = 
       (of_nat a^2)*x3^2 + (of_nat b^2)*x2^2 + (of_nat c^2)*x1^2 + (of_nat d^2)*x0^2 +
       2*(of_nat a)*(of_nat b)*x2*x3 - 2*(of_nat a)*(of_nat c)*x1*x3 - 
       2*(of_nat a)*(of_nat d)*x0*x3 - 2*(of_nat b)*(of_nat c)*x1*x2 - 
       2*(of_nat b)*(of_nat d)*x0*x2 + 2*(of_nat c)*(of_nat d)*x0*x1"
    by (simp add: power2_eq_square algebra_simps)

  (* Combine all the results *)
  have eq5: "((of_nat a)*x0 + (of_nat b)*x1 + (of_nat c)*x2 + (of_nat d)*x3)^2 +
    (-(of_nat b)*x0 + (of_nat a)*x1 - (of_nat d)*x2 + (of_nat c)*x3)^2 +
    (-(of_nat c)*x0 + (of_nat d)*x1 + (of_nat a)*x2 - (of_nat b)*x3)^2 +
    (-(of_nat d)*x0 - (of_nat c)*x1 + (of_nat b)*x2 + (of_nat a)*x3)^2 = 
    ((of_nat a^2)*x0^2 + (of_nat b^2)*x1^2 + (of_nat c^2)*x2^2 + (of_nat d^2)*x3^2) + 
    ((of_nat b^2)*x0^2 + (of_nat a^2)*x1^2 + (of_nat d^2)*x2^2 + (of_nat c^2)*x3^2) + 
    ((of_nat c^2)*x0^2 + (of_nat d^2)*x1^2 + (of_nat a^2)*x2^2 + (of_nat b^2)*x3^2) + 
    ((of_nat d^2)*x0^2 + (of_nat c^2)*x1^2 + (of_nat b^2)*x2^2 + (of_nat a^2)*x3^2)"
    using eq1 eq2 eq3 eq4 by (simp add: algebra_simps)

  have "of_nat(a^2 + b^2 + c^2 + d^2)*(x0^2 + x1^2 + x2^2 + x3^2) =
    ((of_nat a^2)*x0^2 + (of_nat b^2)*x1^2 + (of_nat c^2)*x2^2 + (of_nat d^2)*x3^2) + 
    ((of_nat b^2)*x0^2 + (of_nat a^2)*x1^2 + (of_nat d^2)*x2^2 + (of_nat c^2)*x3^2) + 
    ((of_nat c^2)*x0^2 + (of_nat d^2)*x1^2 + (of_nat a^2)*x2^2 + (of_nat b^2)*x3^2) + 
    ((of_nat d^2)*x0^2 + (of_nat c^2)*x1^2 + (of_nat b^2)*x2^2 + (of_nat a^2)*x3^2)" 
    by (simp add: algebra_simps)

  then have "((of_nat a)*x0 + (of_nat b)*x1 + (of_nat c)*x2 + (of_nat d)*x3)^2 +
    (-(of_nat b)*x0 + (of_nat a)*x1 - (of_nat d)*x2 + (of_nat c)*x3)^2 +
    (-(of_nat c)*x0 + (of_nat d)*x1 + (of_nat a)*x2 - (of_nat b)*x3)^2 +
    (-(of_nat d)*x0  -(of_nat c)*x1 + (of_nat b)*x2 + (of_nat a)*x3)^2 = 
    of_nat(a^2 + b^2 + c^2 + d^2)*(x0^2 + x1^2 + x2^2 + x3^2)"
    using eq5 by (simp add: add.commute add.left_commute)

  thus ?thesis
    by simp
qed

lemma linear_comb_of_y_part_1:
  fixes a :: "nat"
  fixes b :: "nat"
  fixes c :: "nat"
  fixes d :: "nat"
  fixes x :: "rat mat"
  fixes x0 :: "rat"
  fixes x1 :: "rat"
  fixes x2 :: "rat"
  fixes x3 :: "rat"
  fixes i :: "nat"
  fixes m :: "nat"
  assumes "a^2 + b^2 + c^2 + d^2 = 𝗄 - Λ"
           "𝗏 ≥ m" "m > 3" "i ∈ {0..<4}" "x0 = x $$ (m-4,0)" 
          "x1 = x $$ (m-3,0)" "x2 = x $$ (m-2,0)" "x3 = x $$ (m-1,0)"       
  shows "∃e0 e1 e2 e3 :: rat.(∑h ∈ {0..<m}. 
          of_int(N $$ (m-h-1,m-i-1)) * x $$ (m-h-1,0)) =   
          e0 * one_of(y_of((a, b, c, d),(x0, x1, x2, x3))) +
          e1 * two_of(y_of((a, b, c, d),(x0, x1, x2, x3))) +
          e2 * three_of(y_of((a, b, c, d),(x0, x1, x2, x3))) +
          e3 * four_of(y_of((a, b, c, d),(x0, x1, x2, x3))) +
          (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-i-1)) * x $$ (m-h-1,0))"
proof -
  have key: "y_inv_reversible(y_reversible((a, b, c, d),(x0, x1, x2, x3))) = 
         ((a, b, c, d),(x0, x1, x2, x3))" 
  using y_inverses_part_1 assms(1) blocksize_gt_index 
  by (metis less_numeral_extra(3) zero_less_diff)

  let ?D = "of_nat (a^2 + b^2 + c^2 + d^2) :: rat"
  let ?y0 = "one_of(y_of((a, b, c, d),(x0, x1, x2, x3)))" 
  let ?y1 = "two_of(y_of((a, b, c, d),(x0, x1, x2, x3)))"
  let ?y2 = "three_of(y_of((a, b, c, d),(x0, x1, x2, x3)))"
  let ?y3 = "four_of(y_of((a, b, c, d),(x0, x1, x2, x3)))"
  let ?e0 = "of_int(N $$ (m-4,m-i-1)) * (of_nat a)/?D + of_int(N $$ (m-3,m-i-1)) * (of_nat b)/?D +
             of_int(N $$ (m-2,m-i-1)) * (of_nat c)/?D + of_int(N $$ (m-1,m-i-1)) * (of_nat d)/?D"
  let ?e1 = "-of_int(N $$ (m-4,m-i-1)) * (of_nat b)/?D + of_int(N $$ (m-3,m-i-1)) * (of_nat a)/?D -
              of_int(N $$ (m-2,m-i-1)) * (of_nat d)/?D + of_int(N $$ (m-1,m-i-1)) * (of_nat c)/?D"
  let ?e2 = "-of_int(N $$ (m-4,m-i-1)) * (of_nat c)/?D + of_int(N $$ (m-3,m-i-1)) * (of_nat d)/?D +
              of_int(N $$ (m-2,m-i-1)) * (of_nat a)/?D - of_int(N $$ (m-1,m-i-1)) * (of_nat b)/?D"
  let ?e3 = "-of_int(N $$ (m-4,m-i-1)) * (of_nat d)/?D - of_int(N $$ (m-3,m-i-1)) * (of_nat c)/?D +
              of_int(N $$ (m-2,m-i-1)) * (of_nat b)/?D + of_int(N $$ (m-1,m-i-1)) * (of_nat a)/?D"

  have oneof: "x0 = 
    one_of(snd(y_inv_reversible(y_reversible((a, b, c, d),(x0, x1, x2, x3)))))"
    using key by auto
  then have "x0 = ((of_nat a)*?y0 - (of_nat b)*?y1 - (of_nat c)*?y2 - (of_nat d)*?y3)/?D"
    by simp
  then have first_1: "of_int(N $$ (m-4,m-i-1)) * x0 = of_int(N $$ (m-4,m-i-1)) *
    ((of_nat a)*?y0 - (of_nat b)*?y1 - (of_nat c)*?y2 - (of_nat d)*?y3)/?D" 
    by (metis (mono_tags, lifting) times_divide_eq_right)
  have first_2: "of_int(N $$ (m-4,m-i-1)) * ((of_nat a)*?y0 - (of_nat b)*?y1 - (of_nat c)*?y2 - 
    (of_nat d)*?y3)/?D = of_int(N $$ (m-4,m-i-1)) * (of_nat a)*?y0/?D - 
    of_int(N $$ (m-4,m-i-1)) * (of_nat b)*?y1/?D - of_int(N $$ (m-4,m-i-1)) * (of_nat c)*?y2/?D -
    of_int(N $$ (m-4,m-i-1)) * (of_nat d)*?y3/?D" 
    by (simp add: of_rat_diff of_rat_mult right_diff_distrib divide_simps)
  then have first: "of_int(N $$ (m-4,m-i-1)) * x0 = of_int(N $$ (m-4,m-i-1)) * (of_nat a)*?y0/?D - 
    of_int(N $$ (m-4,m-i-1)) * (of_nat b)*?y1/?D - of_int(N $$ (m-4,m-i-1)) * (of_nat c)*?y2/?D - 
    of_int(N $$ (m-4,m-i-1)) * (of_nat d)*?y3/?D" 
    using first_1 first_2 by argo

  have twoof: "x1 = 
    two_of(snd(y_inv_reversible(y_reversible((a, b, c, d),(x0, x1, x2, x3)))))"
    using key by auto
  then have "x1 = ((of_nat b)*?y0 + (of_nat a)*?y1 + (of_nat d)*?y2 - (of_nat c)*?y3)/?D"
    by simp
  then have second_1: "of_int(N $$ (m-3,m-i-1)) * x1 = of_int(N $$ (m-3,m-i-1)) *
    ((of_nat b)*?y0 + (of_nat a)*?y1 + (of_nat d)*?y2 - (of_nat c)*?y3)/?D" 
    by (metis (mono_tags, lifting) times_divide_eq_right)
  have second_2: "of_int(N $$ (m-3,m-i-1)) * ((of_nat b)*?y0 + (of_nat a)*?y1 + (of_nat d)*?y2 - 
    (of_nat c)*?y3)/?D = of_int(N $$ (m-3,m-i-1)) * ((of_nat b)*?y0 + (of_nat a)*?y1 + 
    (of_nat d)*?y2)/?D - of_int(N $$ (m-3,m-i-1)) * (of_nat c)*?y3/?D" 
    by (simp add: of_rat_diff of_rat_mult right_diff_distrib divide_simps)
  have second_3: "of_int(N $$ (m-3,m-i-1)) *((of_nat b)*?y0 + (of_nat a)*?y1 + 
    (of_nat d)*?y2)/?D = (of_int(N $$ (m-3,m-i-1)) * (of_nat b)*?y0 + 
    of_int(N $$ (m-3,m-i-1)) * (of_nat a)*?y1 + of_int(N $$ (m-3,m-i-1)) * (of_nat d)*?y2)/?D"
    by (simp add: of_rat_add of_rat_mult distrib_left)
  have second_4: "(of_int(N $$ (m-3,m-i-1)) * (of_nat b)*?y0 + of_int(N $$ (m-3,m-i-1)) * (of_nat a)*?y1 + 
    of_int(N $$ (m-3,m-i-1)) * (of_nat d)*?y2)/?D = of_int(N $$ (m-3,m-i-1)) * (of_nat b)*?y0/?D + 
    of_int(N $$ (m-3,m-i-1)) * (of_nat a)*?y1/?D + of_int(N $$ (m-3,m-i-1)) * (of_nat d)*?y2/?D"
    by (simp add: of_rat_add of_rat_mult add_divide_distrib)
  then have "(of_int(N $$ (m-3,m-i-1)) * (of_nat b)*?y0 + of_int(N $$ (m-3,m-i-1)) * (of_nat a)*?y1 + 
    of_int(N $$ (m-3,m-i-1)) * (of_nat d)*?y2)/?D - of_int(N $$ (m-3,m-i-1)) * (of_nat c)*?y3/?D = 
    of_int(N $$ (m-3,m-i-1)) * (of_nat b)*?y0/?D + of_int(N $$ (m-3,m-i-1)) * (of_nat a)*?y1/?D + 
    of_int(N $$ (m-3,m-i-1)) * (of_nat d)*?y2/?D - of_int(N $$ (m-3,m-i-1)) * (of_nat c)*?y3/?D" 
    by presburger
  then have second: "of_int(N $$ (m-3,m-i-1)) * x1 = of_int(N $$ (m-3,m-i-1)) * (of_nat b)*?y0/?D +
     of_int(N $$ (m-3,m-i-1)) * (of_nat a)*?y1/?D + of_int(N $$ (m-3,m-i-1)) * (of_nat d)*?y2/?D - 
     of_int(N $$ (m-3,m-i-1)) * (of_nat c)*?y3/?D"
    using second_1 second_2 second_3 second_4 by argo

  have threeof: "x2 = 
    three_of(snd(y_inv_reversible(y_reversible((a, b, c, d),(x0, x1, x2, x3)))))"
    using key by auto
  then have "x2 = ((of_nat c)*?y0 + (of_nat a)*?y2 + (of_nat b)*?y3 - (of_nat d)*?y1)/?D"
    by simp
  then have third_1: "of_int(N $$ (m-2,m-i-1)) * x2 = of_int(N $$ (m-2,m-i-1)) *
    ((of_nat c)*?y0 + (of_nat a)*?y2 + (of_nat b)*?y3 - (of_nat d)*?y1)/?D" 
    by (metis (mono_tags, lifting) times_divide_eq_right) 
  have third_2: "of_int(N $$ (m-2,m-i-1)) * ((of_nat c)*?y0 + (of_nat a)*?y2 + (of_nat b)*?y3 - 
    (of_nat d)*?y1)/?D = of_int(N $$ (m-2,m-i-1)) * ((of_nat c)*?y0 + (of_nat a)*?y2 + (of_nat b)*?y3)/?D - 
    of_int(N $$ (m-2,m-i-1)) * (of_nat d)*?y1/?D" 
    by (simp add: of_rat_diff of_rat_mult right_diff_distrib divide_simps)
  have third_3: "of_int(N $$ (m-2,m-i-1)) *((of_nat c)*?y0 + (of_nat a)*?y2 + 
    (of_nat b)*?y3)/?D = (of_int(N $$ (m-2,m-i-1)) * (of_nat c)*?y0 + 
    of_int(N $$ (m-2,m-i-1)) * (of_nat a)*?y2 + of_int(N $$ (m-2,m-i-1)) * (of_nat b)*?y3)/?D"
    by (simp add: of_rat_add of_rat_mult distrib_left)
  have third_4: "(of_int(N $$ (m-2,m-i-1)) * (of_nat c)*?y0 + of_int(N $$ (m-2,m-i-1)) * (of_nat a)*?y2 + 
    of_int(N $$ (m-2,m-i-1)) * (of_nat b)*?y3)/?D = of_int(N $$ (m-2,m-i-1)) * (of_nat c)*?y0/?D + 
    of_int(N $$ (m-2,m-i-1)) * (of_nat a)*?y2/?D + of_int(N $$ (m-2,m-i-1)) * (of_nat b)*?y3/?D"
    by (simp add: of_rat_add of_rat_mult add_divide_distrib)
  then have "(of_int(N $$ (m-2,m-i-1)) * (of_nat c)*?y0 + of_int(N $$ (m-2,m-i-1)) * (of_nat a)*?y2 + 
    of_int(N $$ (m-2,m-i-1)) * (of_nat b)*?y3)/?D - of_int(N $$ (m-2,m-i-1)) * (of_nat d)*?y1/?D = 
    of_int(N $$ (m-2,m-i-1)) * (of_nat c)*?y0/?D + of_int(N $$ (m-2,m-i-1)) * (of_nat a)*?y2/?D + 
    of_int(N $$ (m-2,m-i-1)) * (of_nat b)*?y3/?D - of_int(N $$ (m-2,m-i-1)) * (of_nat d)*?y1/?D" 
    by presburger
  then have third: "of_int(N $$ (m-2,m-i-1)) * x2 = of_int(N $$ (m-2,m-i-1)) * (of_nat c)*?y0/?D +
     of_int(N $$ (m-2,m-i-1)) * (of_nat a)*?y2/?D + of_int(N $$ (m-2,m-i-1)) * (of_nat b)*?y3/?D - 
     of_int(N $$ (m-2,m-i-1)) * (of_nat d)*?y1/?D"
    using third_1 third_2 third_3 third_4 by argo

  have fourof: "x3 = 
    four_of(snd(y_inv_reversible(y_reversible((a, b, c, d),(x0, x1, x2, x3)))))"
    using key by auto
  then have "x3 = ((of_nat d)*?y0 + (of_nat c)*?y1 + (of_nat a)*?y3 - (of_nat b)*?y2)/?D"
    by simp
  then have fourth_1: "of_int(N $$ (m-1,m-i-1)) * x3 = of_int(N $$ (m-1,m-i-1)) *
    ((of_nat d)*?y0 + (of_nat c)*?y1 + (of_nat a)*?y3 - (of_nat b)*?y2)/?D" 
    by (metis (mono_tags, lifting) times_divide_eq_right) 
  have fourth_2: "of_int(N $$ (m-1,m-i-1)) * ((of_nat d)*?y0 + (of_nat c)*?y1 + (of_nat a)*?y3 - 
    (of_nat b)*?y2)/?D = of_int(N $$ (m-1,m-i-1)) * ((of_nat d)*?y0 + (of_nat c)*?y1 +
    (of_nat a)*?y3)/?D - of_int(N $$ (m-1,m-i-1)) * (of_nat b)*?y2/?D" 
    by (simp add: of_rat_diff of_rat_mult right_diff_distrib divide_simps)
  have fourth_3: "of_int(N $$ (m-1,m-i-1)) *((of_nat d)*?y0 + (of_nat c)*?y1 + 
    (of_nat a)*?y3)/?D = (of_int(N $$ (m-1,m-i-1)) * (of_nat d)*?y0 + 
    of_int(N $$ (m-1,m-i-1)) * (of_nat c)*?y1 + of_int(N $$ (m-1,m-i-1)) * (of_nat a)*?y3)/?D"
    by (simp add: of_rat_add of_rat_mult distrib_left)
  have fourth_4: "(of_int(N $$ (m-1,m-i-1)) * (of_nat d)*?y0 + of_int(N $$ (m-1,m-i-1)) * (of_nat c)*?y1 + 
    of_int(N $$ (m-1,m-i-1)) * (of_nat a)*?y3)/?D = of_int(N $$ (m-1,m-i-1)) * (of_nat d)*?y0/?D + 
    of_int(N $$ (m-1,m-i-1)) * (of_nat c)*?y1/?D + of_int(N $$ (m-1,m-i-1)) * (of_nat a)*?y3/?D"
    by (simp add: of_rat_add of_rat_mult add_divide_distrib)
  then have "(of_int(N $$ (m-1,m-i-1)) * (of_nat d)*?y0 + of_int(N $$ (m-1,m-i-1)) * (of_nat c)*?y1 + 
    of_int(N $$ (m-1,m-i-1)) * (of_nat a)*?y3)/?D - of_int(N $$ (m-1,m-i-1)) * (of_nat b)*?y2/?D = 
    of_int(N $$ (m-1,m-i-1)) * (of_nat d)*?y0/?D + of_int(N $$ (m-1,m-i-1)) * (of_nat c)*?y1/?D + 
    of_int(N $$ (m-1,m-i-1)) * (of_nat a)*?y3/?D - of_int(N $$ (m-1,m-i-1)) * (of_nat b)*?y2/?D" 
    by presburger
  then have fourth: "of_int(N $$ (m-1,m-i-1)) * x3 = of_int(N $$ (m-1,m-i-1)) * (of_nat d)*?y0/?D +
     of_int(N $$ (m-1,m-i-1)) * (of_nat c)*?y1/?D + of_int(N $$ (m-1,m-i-1)) * (of_nat a)*?y3/?D - 
     of_int(N $$ (m-1,m-i-1)) * (of_nat b)*?y2/?D"
    using fourth_1 fourth_2 fourth_3 fourth_4 by argo 

  have sum: "of_int(N $$ (m-4,m-i-1)) * x0 + of_int(N $$ (m-3,m-i-1)) * x1 + 
    of_int(N $$ (m-2,m-i-1)) * x2 + of_int(N $$ (m-1,m-i-1)) * x3 =
    of_int(N $$ (m-4,m-i-1)) * (of_nat a)*?y0/?D - of_int(N $$ (m-4,m-i-1)) * (of_nat b)*?y1/?D - 
    of_int(N $$ (m-4,m-i-1)) * (of_nat c)*?y2/?D - of_int(N $$ (m-4,m-i-1)) * (of_nat d)*?y3/?D +
    of_int(N $$ (m-3,m-i-1)) * (of_nat b)*?y0/?D + of_int(N $$ (m-3,m-i-1)) * (of_nat a)*?y1/?D +
    of_int(N $$ (m-3,m-i-1)) * (of_nat d)*?y2/?D - of_int(N $$ (m-3,m-i-1)) * (of_nat c)*?y3/?D +
    of_int(N $$ (m-2,m-i-1)) * (of_nat c)*?y0/?D - of_int(N $$ (m-2,m-i-1)) * (of_nat d)*?y1/?D + 
    of_int(N $$ (m-2,m-i-1)) * (of_nat a)*?y2/?D + of_int(N $$ (m-2,m-i-1)) * (of_nat b)*?y3/?D + 
    of_int(N $$ (m-1,m-i-1)) * (of_nat d)*?y0/?D + of_int(N $$ (m-1,m-i-1)) * (of_nat c)*?y1/?D - 
    of_int(N $$ (m-1,m-i-1)) * (of_nat b)*?y2/?D + of_int(N $$ (m-1,m-i-1)) * (of_nat a)*?y3/?D"
    using first second third fourth by linarith
  have sumdef: "(∑h ∈ {0..<4}. of_int(N $$ (m-h-1,m-i-1)) * x $$ (m-h-1,0)) = 
        of_int(N $$ (m-4,m-i-1)) * x $$ (m-4,0) + of_int(N $$ (m-3,m-i-1)) * x $$ (m-3,0) + 
        of_int(N $$ (m-2,m-i-1)) * x $$ (m-2,0) + of_int(N $$ (m-1,m-i-1)) * x $$ (m-1,0)" 
    by (simp add: numeral.simps(2,3))
  have split: "{0..<m} = {0..<4} ∪ {4..<m}" using assms(3) by auto
  have inter: "{} = {0..<4} ∩ {4..<m}" by auto
  have "(∑h ∈ {0..<m}. of_int(N $$ (m-h-1,m-i-1)) * x $$ (m-h-1,0)) =
        (∑h ∈ {0..<4}. of_int(N $$ (m-h-1,m-i-1)) * x $$ (m-h-1,0)) + 
        (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-i-1)) * x $$ (m-h-1,0))"
    using split inter sum.union_disjoint[of "{0..<4}" "{4..<m}" "λ h . 
    (of_int(N $$ (m-h-1,m-i-1)) * x $$ (m-h-1,0))"] 
    by (metis (no_types, lifting) finite_atLeastLessThan)
  then have "(∑h ∈ {0..<m}. of_int(N $$ (m-h-1,m-i-1)) * x $$ (m-h-1,0)) = 
        of_int(N $$ (m-4,m-i-1)) * x0 + of_int(N $$ (m-3,m-i-1)) * x1 +
        of_int(N $$ (m-2,m-i-1)) * x2 + of_int(N $$ (m-1,m-i-1)) * x3 +
        (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-i-1)) * x $$ (m-h-1,0))"
    using sumdef assms(4-8) by argo
  then have "(∑h ∈ {0..<m}. of_int(N $$ (m-h-1,m-i-1)) * x $$ (m-h-1,0)) =   
    of_int(N $$ (m-4,m-i-1)) * (of_nat a)*?y0/?D - of_int(N $$ (m-4,m-i-1)) * (of_nat b)*?y1/?D - 
    of_int(N $$ (m-4,m-i-1)) * (of_nat c)*?y2/?D - of_int(N $$ (m-4,m-i-1)) * (of_nat d)*?y3/?D +
    of_int(N $$ (m-3,m-i-1)) * (of_nat b)*?y0/?D + of_int(N $$ (m-3,m-i-1)) * (of_nat a)*?y1/?D +
    of_int(N $$ (m-3,m-i-1)) * (of_nat d)*?y2/?D - of_int(N $$ (m-3,m-i-1)) * (of_nat c)*?y3/?D +
    of_int(N $$ (m-2,m-i-1)) * (of_nat c)*?y0/?D - of_int(N $$ (m-2,m-i-1)) * (of_nat d)*?y1/?D + 
    of_int(N $$ (m-2,m-i-1)) * (of_nat a)*?y2/?D + of_int(N $$ (m-2,m-i-1)) * (of_nat b)*?y3/?D + 
    of_int(N $$ (m-1,m-i-1)) * (of_nat d)*?y0/?D + of_int(N $$ (m-1,m-i-1)) * (of_nat c)*?y1/?D - 
    of_int(N $$ (m-1,m-i-1)) * (of_nat b)*?y2/?D + of_int(N $$ (m-1,m-i-1)) * (of_nat a)*?y3/?D +
    (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-i-1)) * x $$ (m-h-1,0))" using sum by argo
  then have "(∑h ∈ {0..<m}. of_int(N $$ (m-h-1,m-i-1)) * x $$ (m-h-1,0)) =   
    of_int(N $$ (m-4,m-i-1)) * (of_nat a)*?y0/?D + of_int(N $$ (m-3,m-i-1)) * (of_nat b)*?y0/?D +
    of_int(N $$ (m-2,m-i-1)) * (of_nat c)*?y0/?D + of_int(N $$ (m-1,m-i-1)) * (of_nat d)*?y0/?D -
    of_int(N $$ (m-4,m-i-1)) * (of_nat b)*?y1/?D + of_int(N $$ (m-3,m-i-1)) * (of_nat a)*?y1/?D -
    of_int(N $$ (m-2,m-i-1)) * (of_nat d)*?y1/?D + of_int(N $$ (m-1,m-i-1)) * (of_nat c)*?y1/?D -
    of_int(N $$ (m-4,m-i-1)) * (of_nat c)*?y2/?D + of_int(N $$ (m-3,m-i-1)) * (of_nat d)*?y2/?D +
    of_int(N $$ (m-2,m-i-1)) * (of_nat a)*?y2/?D - of_int(N $$ (m-1,m-i-1)) * (of_nat b)*?y2/?D -
    of_int(N $$ (m-4,m-i-1)) * (of_nat d)*?y3/?D - of_int(N $$ (m-3,m-i-1)) * (of_nat c)*?y3/?D +
    of_int(N $$ (m-2,m-i-1)) * (of_nat b)*?y3/?D + of_int(N $$ (m-1,m-i-1)) * (of_nat a)*?y3/?D +
    (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-i-1)) * x $$ (m-h-1,0))" by (simp add: algebra_simps)
  then have "(∑h ∈ {0..<m}. of_int(N $$ (m-h-1,m-i-1)) * x $$ (m-h-1,0)) = 
    (of_int(N $$ (m-4,m-i-1)) * (of_nat a)/?D + of_int(N $$ (m-3,m-i-1)) * (of_nat b)/?D +
     of_int(N $$ (m-2,m-i-1)) * (of_nat c)/?D + of_int(N $$ (m-1,m-i-1)) * (of_nat d)/?D) * ?y0 +
    (-of_int(N $$ (m-4,m-i-1)) * (of_nat b)/?D + of_int(N $$ (m-3,m-i-1)) * (of_nat a)/?D -
     of_int(N $$ (m-2,m-i-1)) * (of_nat d)/?D + of_int(N $$ (m-1,m-i-1)) * (of_nat c)/?D) * ?y1 +
    (-of_int(N $$ (m-4,m-i-1)) * (of_nat c)/?D + of_int(N $$ (m-3,m-i-1)) * (of_nat d)/?D +
     of_int(N $$ (m-2,m-i-1)) * (of_nat a)/?D - of_int(N $$ (m-1,m-i-1)) * (of_nat b)/?D) * ?y2 +
    (-of_int(N $$ (m-4,m-i-1)) * (of_nat d)/?D - of_int(N $$ (m-3,m-i-1)) * (of_nat c)/?D +
     of_int(N $$ (m-2,m-i-1)) * (of_nat b)/?D + of_int(N $$ (m-1,m-i-1)) * (of_nat a)/?D) * ?y3 +
    (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-i-1)) * x $$ (m-h-1,0))" by (simp add: algebra_simps)
  then have "(∑h ∈ {0..<m}. of_int(N $$ (m-h-1,m-i-1)) * x $$ (m-h-1,0)) = 
    ?e00 * ?y0 + ?e01 * ?y1 + ?e02 * ?y2 + ?e03 * ?y3 +
    (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-i-1)) * x $$ (m-h-1,0))" by blast
  then show ?thesis by blast
qed

lemma linear_comb_of_y_part_2:
  fixes a :: "nat"
  fixes b :: "nat"
  fixes c :: "nat"
  fixes d :: "nat"
  fixes y0 :: "rat"
  fixes y1 :: "rat"
  fixes y2 :: "rat"
  fixes y3 :: "rat"
  fixes x :: "rat mat"
  fixes x0 :: "rat"
  fixes x1 :: "rat"
  fixes x2 :: "rat"
  fixes x3 :: "rat"
  fixes i :: "nat"
  fixes m :: "nat"
  assumes "a^2 + b^2 + c^2 + d^2 = (𝗄 - Λ)"
          "𝗏 ≥ m" "m > 3" "i ∈ {0..<4}" "x0 = x $$ (m-4,0)" 
          "x1 = x $$ (m-3,0)" "x2 = x $$ (m-2,0)" "x3 = x $$ (m-1,0)"   
          "x0 = one_of(y_inv_of((a, b, c, d),(y0, y1, y2, y3)))"
          "x1 = two_of(y_inv_of((a, b, c, d),(y0, y1, y2, y3)))"
          "x2 = three_of(y_inv_of((a, b, c, d),(y0, y1, y2, y3)))"
          "x3 = four_of(y_inv_of((a, b, c, d),(y0, y1, y2, y3)))"
  shows "∃e0 e1 e2 e3 :: rat.(∑h ∈ {0..<m}. of_int(N $$ (m-h-1,m-i-1)) * x $$ (m-h-1,0)) = 
    e0 * y0 + e1 * y1 + e2 * y2 + e3 * y3 +
    (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-i-1)) * x $$ (m-h-1,0))"
proof -
  
  have "∃e0 e1 e2 e3 :: rat.(∑h ∈ {0..<m}. 
          of_int(N $$ (m-h-1,m-i-1)) * x $$ (m-h-1,0)) =   
          e0 * one_of(y_of((a, b, c, d),(x0, x1, x2, x3))) +
          e1 * two_of(y_of((a, b, c, d),(x0, x1, x2, x3))) +
          e2 * three_of(y_of((a, b, c, d),(x0, x1, x2, x3))) +
          e3 * four_of(y_of((a, b, c, d),(x0, x1, x2, x3))) +
          (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-i-1)) * x $$ (m-h-1,0))"
     using linear_comb_of_y_part_1 assms(1-12) by fast
  then have "∃e0 e1 e2 e3 :: rat.(∑h ∈ {0..<m}. 
          of_int(N $$ (m-h-1,m-i-1)) * x $$ (m-h-1,0)) =   
          e0 * one_of(y_of((a, b, c, d),(x0, x1, x2, x3))) +
          e1 * two_of(y_of((a, b, c, d),(x0, x1, x2, x3))) +
          e2 * three_of(y_of((a, b, c, d),(x0, x1, x2, x3))) +
          e3 * four_of(y_of((a, b, c, d),(x0, x1, x2, x3))) +
          (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-i-1)) * x $$ (m-h-1,0))"
    by simp

   then obtain e0 e1 e2 e3 where eq1:
    "(∑h ∈ {0..<m}. of_int(N $$ (m-h-1,m-i-1)) * x $$ (m-h-1,0)) = 
    e0 * one_of(y_of((a, b, c, d),(x0, x1, x2, x3))) +
    e1 * two_of(y_of((a, b, c, d),(x0, x1, x2, x3))) +
    e2 * three_of(y_of((a, b, c, d),(x0, x1, x2, x3))) +
    e3 * four_of(y_of((a, b, c, d),(x0, x1, x2, x3))) +
    (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-i-1)) * x $$ (m-h-1,0))"
     by fast

  have "((a, b, c, d),(x0, x1, x2, x3)) = 
        y_inv_reversible((a, b, c, d),(y0, y1, y2, y3))"
    using assms(9-12) by simp
  then have "y_reversible((a, b, c, d),(x0, x1, x2, x3)) = 
        y_reversible(y_inv_reversible((a, b, c, d),(y0, y1, y2, y3)))"
    by simp
  then have eq2: "y_reversible((a, b, c, d),(x0, x1, x2, x3)) =
    ((a, b, c, d),(y0, y1, y2, y3))" 
    using y_inverses_part_2 assms(1) assms(9-12) blocksize_gt_index 
    by (metis less_numeral_extra(3) zero_less_diff) 
  have eq3: "y0 = one_of(y_of((a, b, c, d),(x0, x1, x2, x3)))" 
    using eq2 by simp
  have eq4: "y1 = two_of(y_of((a, b, c, d),(x0, x1, x2, x3)))" 
    using eq2 by simp
  have eq5: "y2 = three_of(y_of((a, b, c, d),(x0, x1, x2, x3)))" 
    using eq2 by simp
  have eq6: "y3 = four_of(y_of((a, b, c, d),(x0, x1, x2, x3)))" 
    using eq2 by simp
  have "e0 * y0 + e1 * y1 + e2 * y2 + e3 * y3 = 
    e0 * one_of(y_of((a, b, c, d),(x0, x1, x2, x3))) +
    e1 * two_of(y_of((a, b, c, d),(x0, x1, x2, x3))) +
    e2 * three_of(y_of((a, b, c, d),(x0, x1, x2, x3))) +
    e3 * four_of(y_of((a, b, c, d),(x0, x1, x2, x3)))"
    using eq3 eq4 eq5 eq6 by simp
  thus ?thesis using eq1 by (metis (no_types, lifting))
qed

lemma lagrange_identity_x:
  fixes a :: "nat"
  fixes b :: "nat"
  fixes c :: "nat"
  fixes d :: "nat"
  fixes x0 :: "rat"
  fixes x1 :: "rat"
  fixes x2 :: "rat"
  fixes x3 :: "rat"
  fixes x :: "rat mat"
  fixes i :: "nat"
  fixes m :: "nat"
  assumes "a^2 + b^2 + c^2 + d^2 = 𝗄 - Λ"
          "𝗏 ≥ m" "m > 3" "i ∈ {0..<4}" "x0 = x $$ (m-4,0)" 
          "x1 = x $$ (m-3,0)" "x2 = x $$ (m-2,0)" "x3 = x $$ (m-1,0)"
  shows "of_int(𝗄 - Λ) * (∑j ∈ {0..<m}. (x $$ (m-j-1, 0))^2) = 
         of_int(𝗄 - Λ) * (∑j ∈ {4..<m}. (x $$ (m-j-1, 0))^2) +
         (one_of(y_of((a, b, c, d),(x0, x1, x2, x3)))^2 +
          two_of(y_of((a, b, c, d), (x0, x1, x2, x3)))^2 +
          three_of(y_of((a, b, c, d), (x0, x1, x2, x3)))^2 +
          four_of(y_of((a, b, c, d), (x0, x1, x2, x3)))^2)"
proof -
  have eq0: "x0^2 = (x $$ (m-4,0))^2"
    using assms(5) by (simp add: of_rat_power)
  have eq1: "x1^2 = (x $$ (m-3,0))^2"
    using assms(6) by (simp add: of_rat_power)
  have eq2: "x2^2 = (x $$ (m-2,0))^2"
    using assms(7) by (simp add: of_rat_power)
  have eq3: "x3^2 = (x $$ (m-1,0))^2"
    using assms(8) by (simp add: of_rat_power)
  have eq: "x0^2 + x1^2 + x2^2 + x3^2 = 
    (x $$ (m-4,0))^2 + (x $$ (m-3,0))^2 + (x $$ (m-2,0))^2 + (x $$ (m-1,0))^2"
    using eq0 eq1 eq2 eq3 by (simp add: of_rat_add)
  have "one_of(y_of((a, b, c, d),(x0, x1, x2, x3)))^2 +
          two_of(y_of((a, b, c, d), (x0, x1, x2, x3)))^2 +
          three_of(y_of((a, b, c, d), (x0, x1, x2, x3)))^2 +
          four_of(y_of((a, b, c, d), (x0, x1, x2, x3)))^2 = 
          of_nat (a^2 + b^2 + c^2 + d^2) * (x0^2 + x1^2 + x2^2 + x3^2)" 
    using lagrange_trans_of_4_identity[of a b c d x0 x1 x2 x3] assms(1-8) by blast
  then have "one_of(y_of((a, b, c, d),(x0, x1, x2, x3)))^2 +
          two_of(y_of((a, b, c, d), (x0, x1, x2, x3)))^2 +
          three_of(y_of((a, b, c, d), (x0, x1, x2, x3)))^2 +
          four_of(y_of((a, b, c, d), (x0, x1, x2, x3)))^2 = 
          of_nat (𝗄 - Λ) * (x0^2 + x1^2 + x2^2 + x3^2)" using assms(1)
    by presburger
  then have keyform: "one_of(y_of((a, b, c, d),(x0, x1, x2, x3)))^2 +
          two_of(y_of((a, b, c, d), (x0, x1, x2, x3)))^2 +
          three_of(y_of((a, b, c, d), (x0, x1, x2, x3)))^2 +
          four_of(y_of((a, b, c, d), (x0, x1, x2, x3)))^2 = 
          of_int(𝗄 - Λ) * ((x $$ (m-1,0))^2 + (x $$ (m-2,0))^2 +
          (x $$ (m-3,0))^2 + (x $$ (m-4,0))^2)" using eq by simp
  have sumdef: "(∑j ∈ {0..<4}. (x $$ (m-j-1, 0))^2) = (x $$ (m-1,0))^2 + 
        (x $$ (m-2,0))^2 + (x $$ (m-3,0))^2 + (x $$ (m-4,0))^2" by (simp add: numeral.simps(2,3))
  have split: "{0..<m} = {0..<4} ∪ {4..<m}" using assms(3) by auto
  have inter: "{} = {0..<4} ∩ {4..<m}" by auto
  have "(∑j ∈ {0..<m}. (x $$ (m-j-1, 0))^2) =
        (∑j ∈ {0..<4}. (x $$ (m-j-1, 0))^2) + 
        (∑j ∈ {4..<m}. (x $$ (m-j-1, 0))^2)"
    using split inter sum.union_disjoint[of "{0..<4}" "{4..<m}" "λ j . (x $$ (m-j-1, 0))^2"] 
    by (metis (no_types, lifting) finite_atLeastLessThan)
  then have "of_int (𝗄 - Λ) * (∑j ∈ {0..<m}. (x $$ (m-j-1, 0))^2) =
        of_int (𝗄 - Λ) * (∑j ∈ {0..<4}. (x $$ (m-j-1, 0))^2) + 
        of_int (𝗄 - Λ) * (∑j ∈ {4..<m}. (x $$ (m-j-1, 0))^2)" using algebra_simps by simp
  then have "of_int (𝗄 - Λ) * (∑j ∈ {0..<m}. (x $$ (m-j-1, 0))^2) =
        of_int (𝗄 - Λ) * (∑j ∈ {4..<m}. (x $$ (m-j-1, 0))^2) +
        of_int (𝗄 - Λ) * ((x $$ (m-1,0))^2 + (x $$ (m-2,0))^2 + (x $$ (m-3,0))^2 + (x $$ (m-4,0))^2)"
    using sumdef algebra_simps by auto
  then have "of_nat(𝗄 - Λ) * (∑j ∈ {0..<m}. (x $$ (m-j-1, 0))^2) = 
             of_nat(𝗄 - Λ) * (∑j ∈ {4..<m}. (x $$ (m-j-1, 0))^2) +
            (one_of(y_of((a, b, c, d),(x0, x1, x2, x3)))^2 +
             two_of(y_of((a, b, c, d), (x0, x1, x2, x3)))^2 +
             three_of(y_of((a, b, c, d), (x0, x1, x2, x3)))^2 +
             four_of(y_of((a, b, c, d), (x0, x1, x2, x3)))^2)"
    using keyform algebra_simps by linarith
  thus ?thesis by simp
qed

lemma lagrange_identity_y:
  fixes a :: "nat"
  fixes b :: "nat"
  fixes c :: "nat"
  fixes d :: "nat"
  fixes x0 :: "rat"
  fixes x1 :: "rat"
  fixes x2 :: "rat"
  fixes x3 :: "rat"
  fixes y0 :: "rat"
  fixes y1 :: "rat"
  fixes y2 :: "rat"
  fixes y3 :: "rat"
  fixes x :: "rat mat"
  fixes i :: "nat"
  fixes m :: "nat"
  assumes "a^2 + b^2 + c^2 + d^2 = 𝗄 - Λ"
          "𝗏 ≥ m" "m > 3" "i ∈ {0..<4}" "x0 = x $$ (m-4,0)" 
          "x1 = x $$ (m-3,0)" "x2 = x $$ (m-2,0)" "x3 = x $$ (m-1,0)"
          "x0 = one_of(y_inv_of((a, b, c, d),(y0, y1, y2, y3)))"
          "x1 = two_of(y_inv_of((a, b, c, d),(y0, y1, y2, y3)))"
          "x2 = three_of(y_inv_of((a, b, c, d),(y0, y1, y2, y3)))"
          "x3 = four_of(y_inv_of((a, b, c, d),(y0, y1, y2, y3)))"
  shows   "of_int (𝗄 - Λ) * (∑j ∈ {0..<m}. (x $$ (m-j-1, 0))^2) = 
           of_int (𝗄 - Λ) * (∑j ∈ {4..<m}. (x $$ (m-j-1, 0))^2) +
           y0^2 + y1^2 + y2^2 + y3^2"
proof -
  have eq1: "of_int (𝗄 - Λ) * (∑j ∈ {0..<m}. (x $$ (m-j-1, 0))^2) = 
             of_int (𝗄 - Λ) * (∑j ∈ {4..<m}. (x $$ (m-j-1, 0))^2) +
             (one_of(y_of((a, b, c, d),(x0, x1, x2, x3)))^2 +
              two_of(y_of((a, b, c, d), (x0, x1, x2, x3)))^2 +
              three_of(y_of((a, b, c, d), (x0, x1, x2, x3)))^2 +
              four_of(y_of((a, b, c, d), (x0, x1, x2, x3)))^2)"
    using assms lagrange_identity_x by metis
  have "((a, b, c, d),(x0, x1, x2, x3)) = 
        y_inv_reversible((a, b, c, d),(y0, y1, y2, y3))"
    using assms by simp
  then have "y_reversible((a, b, c, d),(x0, x1, x2, x3)) = 
        y_reversible(y_inv_reversible((a, b, c, d),(y0, y1, y2, y3)))"
    by simp
  then have eq2: "y_reversible((a, b, c, d),(x0, x1, x2, x3)) =
    ((a, b, c, d),(y0, y1, y2, y3))" 
        using y_inverses_part_2 assms blocksize_gt_index 
        by (metis (no_types, lifting) neq0_conv zero_less_diff)
  have eq3: "y0^2 = one_of(y_of((a, b, c, d),(x0, x1, x2, x3)))^2" 
    using eq2 by simp
  have eq4: "y1^2 = two_of(y_of((a, b, c, d),(x0, x1, x2, x3)))^2" 
    using eq2 by simp
  have eq5: "y2^2 = three_of(y_of((a, b, c, d),(x0, x1, x2, x3)))^2" 
    using eq2 by simp
  have eq6: "y3^2 = four_of(y_of((a, b, c, d),(x0, x1, x2, x3)))^2" 
    using eq2 by simp
  have "y0^2 + y1^2 + y2^2 + y3^2 = 
        one_of(y_of((a, b, c, d),(x0, x1, x2, x3)))^2 +
        two_of(y_of((a, b, c, d), (x0, x1, x2, x3)))^2 +
        three_of(y_of((a, b, c, d), (x0, x1, x2, x3)))^2 +
        four_of(y_of((a, b, c, d), (x0, x1, x2, x3)))^2"
    using eq3 eq4 eq5 eq6 by simp
  thus ?thesis using eq1 by simp
qed

lemma induction_step_0:
  fixes a :: "nat"
  fixes b :: "nat"
  fixes c :: "nat"
  fixes d :: "nat"
  fixes x0 :: "rat"
  fixes x1 :: "rat"
  fixes x2 :: "rat"
  fixes x3 :: "rat"
  fixes y0 :: "rat"
  fixes y1 :: "rat"
  fixes y2 :: "rat"
  fixes y3 :: "rat"
  fixes x :: "rat mat"
  fixes m :: "nat"
  assumes "of_nat(a^2 + b^2 + c^2 + d^2) = of_int(𝗄 - Λ)" "𝗏 ≥ m" "m > 3"        
        "(∑h ∈ {0..<m}. of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) = 
         e00 * y0 + e10 * y1 + e20 * y2 + e30 * y3 +
         (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0))"
        "y0 = (if e00 = 1 then -(e10 * y1 + e20 * y2 + e30 * y3 +
        (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
        (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-4)) * x $$ (h,0)))/2 else  
        (e10 * y1 + e20 * y2 + e30 * y3 +
        (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
        (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-4)) * x $$ (h,0)))/(1-e00))"
  shows "y0^2 = ((∑h ∈ {0..<m}. of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
                 (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-4)) * x $$ (h,0)))^2"
proof -
  have "y0^2 = ((∑h ∈ {0..<m}. of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
               (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-4)) * x $$ (h,0)))^2"
   proof (cases "e00 = 1")
     case True   
    then have "y0 = -(e10 * y1 + e20 * y2 + e30 * y3 +
                 (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
                 (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-4)) * x $$ (h,0)))/2"
      using assms(5) by auto
    then have eq: "-y0 = e00 * y0 + e10 * y1 + e20 * y2 + e30 * y3 +
                 (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
                 (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-4)) * x $$ (h,0))"
      using True by (simp add: algebra_simps)
    have "e00 * y0 + e10 * y1 + e20 * y2 + e30 * y3 +
          (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0))  = 
          (∑h ∈ {0..<m}. of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0))"
      using assms(4) by simp
    then have "-y0 = (∑h ∈ {0..<m}. of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
              (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-4)) * x $$ (h,0))"
      using eq by simp
    then have "(-y0)^2 = ((∑h ∈ {0..<m}. of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
              (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-4)) * x $$ (h,0)))^2"
      by argo
    then show ?thesis
      by simp
   next
    case False
    then have "y0 = (e10 * y1 + e20 * y2 + e30 * y3 +
                 (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
                 (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-4)) * x $$ (h,0))) / (1 - e00)"
      using assms(5) by auto
    then have "(1 - e00) * y0 = e10 * y1 + e20 * y2 + e30 * y3 +
                 (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
                 (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-4)) * x $$ (h,0))"
      using False by auto
    then have eq2: "y0 = e00 * y0 + e10 * y1 + e20 * y2 + e30 * y3 +
                 (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
                 (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-4)) * x $$ (h,0))"
      by (simp add: algebra_simps)
    then have "y0 = (∑h ∈ {0..<m}. of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
              (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-4)) * x $$ (h,0))"
      using assms(4) by simp     
    then have "y0^2 = ((∑h ∈ {0..<m}. of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
              (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-4)) * x $$ (h,0)))^2"
      by simp
    then show ?thesis
      by (simp add: algebra_simps)
  qed
  thus ?thesis by simp
qed

lemma induction_step_1:
  fixes a :: "nat"
  fixes b :: "nat"
  fixes c :: "nat"
  fixes d :: "nat"
  fixes x0 :: "rat"
  fixes x1 :: "rat"
  fixes x2 :: "rat"
  fixes x3 :: "rat"
  fixes y0 :: "rat"
  fixes y1 :: "rat"
  fixes y2 :: "rat"
  fixes y3 :: "rat"
  fixes x :: "rat mat"
  fixes m :: "nat"
  assumes "of_nat(a^2 + b^2 + c^2 + d^2) = of_int(𝗄 - Λ)" "𝗏 ≥ m" "m > 3"
          "(∑h ∈ {0..<m}. of_int(N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) = 
            e01 * y0 + e11 * y1 + e21 * y2 + e31 * y3 +
           (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-3)) * x $$ (m-h-1,0))"
           "y1 = (if e11 = 1 then -(e01 * y0 + e21 * y2 + e31 * y3 +
           (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
           (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-3)) * x $$ (h,0)))/2 else  
           (e01 * y0 + e21 * y2 + e31 * y3 +
           (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
           (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-3)) * x $$ (h,0)))/(1-e11))"
  shows "y1^2 = ((∑h ∈ {0..<m}. of_int(N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
           (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-3)) * x $$ (h,0)))^2"
proof -
  have "y1^2 = ((∑h ∈ {0..<m}. of_int(N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
              (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-3)) * x $$ (h,0)))^2"
   proof (cases "e11 = 1")
     case True   
    then have "y1 = -(e01 * y0 + e21 * y2 + e31 * y3 +
                 (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
                 (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-3)) * x $$ (h,0)))/2"
      using assms(5) by auto
    then have eq: "-y1 = e01 * y0 + e11 * y1 + e21 * y2 + e31 * y3 +
                 (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
                 (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-3)) * x $$ (h,0))"
      using True by (simp add: algebra_simps)
    have "e01 * y0 + e11 * y1 + e21 * y2 + e31 * y3 +
          (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-3)) * x $$ (m-h-1,0))  = 
          (∑h ∈ {0..<m}. of_int(N $$ (m-h-1,m-3)) * x $$ (m-h-1,0))"
      using assms(4) by simp
    then have "-y1 = (∑h ∈ {0..<m}. of_int(N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
              (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-3)) * x $$ (h,0))"
      using eq by simp
    then have "(-y1)^2 = ((∑h ∈ {0..<m}. of_int(N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
              (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-3)) * x $$ (h,0)))^2"
      by argo
    then show ?thesis
      by auto
   next
    case False
    then have "y1 = (e01 * y0 + e21 * y2 + e31 * y3 +
                 (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
                 (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-3)) * x $$ (h,0))) / (1 - e11)"
      using assms(5) by auto
    then have "(1 - e11) * y1 = e01 * y0 + e21 * y2 + e31 * y3 +
                 (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
                 (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-3)) * x $$ (h,0))"
      using False by auto
    then have eq2: "y1 = e01 * y0 + e11 * y1 + e21 * y2 + e31 * y3 +
                 (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
                 (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-3)) * x $$ (h,0))"
      by (simp add: algebra_simps)
    then have "y1 = (∑h ∈ {0..<m}. of_int(N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
              (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-3)) * x $$ (h,0))"
      using assms(4) by simp     
    then have "y1^2 = ((∑h ∈ {0..<m}. of_int(N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
              (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-3)) * x $$ (h,0)))^2"
      by simp
    then show ?thesis
      by (simp add: algebra_simps)
  qed
  thus ?thesis by simp
qed

lemma induction_step_2:
  fixes a :: "nat"
  fixes b :: "nat"
  fixes c :: "nat"
  fixes d :: "nat"
  fixes x0 :: "rat"
  fixes x1 :: "rat"
  fixes x2 :: "rat"
  fixes x3 :: "rat"
  fixes y0 :: "rat"
  fixes y1 :: "rat"
  fixes y2 :: "rat"
  fixes y3 :: "rat"
  fixes x :: "rat mat"
  fixes m :: "nat"
  assumes "of_nat(a^2 + b^2 + c^2 + d^2) = of_int(𝗄 - Λ)" "𝗏 ≥ m" "m > 3"
          "(∑h ∈ {0..<m}. of_int(N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) = 
           e02 * y0 + e12 * y1 + e22 * y2 + e32 * y3 +
           (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-2)) * x $$ (m-h-1,0))"
          "y2 = (if e22 = 1 then -(e02 * y0 + e12 * y1 + e32 * y3 +
           (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
           (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-2)) * x $$ (h,0)))/2 else  
           (e02 * y0 + e12 * y1 + e32 * y3 +
           (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
           (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-2)) * x $$ (h,0)))/(1-e22))" 
  shows "y2^2 = ((∑h ∈ {0..<m}. of_int(N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
           (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-2)) * x $$ (h,0)))^2"
proof -
  have "y2^2 = ((∑h ∈ {0..<m}. of_int(N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
               (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-2)) * x $$ (h,0)))^2"
   proof (cases "e22 = 1")
     case True   
    then have "y2 = -(e02 * y0 + e12 * y1 + e32 * y3 +
                 (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
                 (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-2)) * x $$ (h,0)))/2"
      using assms(5) by auto
    then have eq: "-y2 = e02 * y0 + e12 * y1 + e22 * y2 + e32 * y3 +
                 (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
                 (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-2)) * x $$ (h,0))"
      using True by (simp add: algebra_simps)
    have "e02 * y0 + e12 * y1 + e22 * y2 + e32 * y3 +
          (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-2)) * x $$ (m-h-1,0))  = 
          (∑h ∈ {0..<m}. of_int(N $$ (m-h-1,m-2)) * x $$ (m-h-1,0))"
      using assms(4) by simp
    then have "-y2 = (∑h ∈ {0..<m}. of_int(N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
              (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-2)) * x $$ (h,0))"
      using eq by simp
    then have "(-y2)^2 = ((∑h ∈ {0..<m}. of_int(N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
              (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-2)) * x $$ (h,0)))^2"
      by argo
    then show ?thesis
      by simp
   next
    case False
    then have "y2 = (e02 * y0 + e12 * y1 + e32 * y3 +
                 (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
                 (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-2)) * x $$ (h,0))) / (1 - e22)"
      using assms(5) by auto
    then have "(1 - e22) * y2 = e02 * y0 + e12 * y1 + e32 * y3 +
                 (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
                 (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-2)) * x $$ (h,0))"
      using False by auto
    then have eq2: "y2 = e02 * y0 + e12 * y1 + e22 * y2 + e32 * y3 +
                 (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
                 (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-2)) * x $$ (h,0))"
      by (simp add: algebra_simps)
    then have "y2 = (∑h ∈ {0..<m}. of_int(N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
              (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-2)) * x $$ (h,0))"
      using assms(4) by simp     
    then have "y2^2 = ((∑h ∈ {0..<m}. of_int(N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
              (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-2)) * x $$ (h,0)))^2"
      by simp
    then show ?thesis
      by (simp add: algebra_simps)
  qed
  thus ?thesis by simp
qed

lemma induction_step_3:
  fixes a :: "nat"
  fixes b :: "nat"
  fixes c :: "nat"
  fixes d :: "nat"
  fixes x0 :: "rat"
  fixes x1 :: "rat"
  fixes x2 :: "rat"
  fixes x3 :: "rat"
  fixes y0 :: "rat"
  fixes y1 :: "rat"
  fixes y2 :: "rat"
  fixes y3 :: "rat"
  fixes x :: "rat mat"
  fixes m :: "nat"
  assumes "of_nat(a^2 + b^2 + c^2 + d^2) = of_int(𝗄 - Λ)" "𝗏 ≥ m" "m > 3"
          "(∑h ∈ {0..<m}. of_int(N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) = 
           e03 * y0 + e13 * y1 + e23 * y2 + e33 * y3 +
           (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-1)) * x $$ (m-h-1,0))"
          "y3 = (if e33 = 1 then -(e03 * y0 + e13 * y1 + e23 * y2 +
           (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
           (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-1)) * x $$ (h,0)))/2 else  
           (e03 * y0 + e13 * y1 + e23 * y2 +
           (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
           (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-1)) * x $$ (h,0)))/(1-e33))"
  shows "y3^2 = ((∑h ∈ {0..<m}. of_int(N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
           (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-1)) * x $$ (h,0)))^2"
proof -
  have first_fact: "y3^2 = ((∑h ∈ {0..<m}. of_int(N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
              (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-1)) * x $$ (h,0)))^2"
   proof (cases "e33 = 1")
     case True   
    then have "y3 = -(e03 * y0 + e13 * y1 + e23 * y2 +
                 (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
                 (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-1)) * x $$ (h,0)))/2"
      using assms(5) by auto
    then have eq: "-y3 = e03 * y0 + e13 * y1 + e23 * y2 + e33 * y3 +
                 (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
                 (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-1)) * x $$ (h,0))"
      using True by (simp add: algebra_simps)
    have "e03 * y0 + e13 * y1 + e23 * y2 + e33 * y3 +
          (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-1)) * x $$ (m-h-1,0))  = 
          (∑h ∈ {0..<m}. of_int(N $$ (m-h-1,m-1)) * x $$ (m-h-1,0))"
      using assms(4) by simp
    then have "-y3 = (∑h ∈ {0..<m}. of_int(N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
              (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-1)) * x $$ (h,0))"
      using eq by simp
    then have "(-y3)^2 = ((∑h ∈ {0..<m}. of_int(N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
              (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-1)) * x $$ (h,0)))^2"
      by argo
    then show ?thesis
      by simp
   next
    case False
    then have "y3 = (e03 * y0 + e13 * y1 + e23 * y2 +
                 (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
                 (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-1)) * x $$ (h,0))) / (1 - e33)"
      using assms(5) by auto
    then have "(1 - e33) * y3 = e03 * y0 + e13 * y1 + e23 * y2 +
                 (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
                 (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-1)) * x $$ (h,0))"
      using False by auto
    then have eq2: "y3 = e03 * y0 + e13 * y1 + e23 * y2 + e33 * y3 +
                 (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
                 (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-1)) * x $$ (h,0))"
      by (simp add: algebra_simps)
    then have "y3 = (∑h ∈ {0..<m}. of_int(N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
              (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-1)) * x $$ (h,0))"
      using assms(4) by simp     
    then have "y3^2 = ((∑h ∈ {0..<m}. of_int(N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
              (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-1)) * x $$ (h,0)))^2"
      by simp
    then show ?thesis
      by (simp add: algebra_simps)
  qed
  thus ?thesis by simp
qed

lemma induction_step_0_explicit:
  fixes e00 e10 e20 e30 :: rat
  fixes y0 y1 y2 y3 :: rat
  fixes x :: "rat mat"
  fixes m :: nat
  assumes L0:
    "(∑h∈{0..<m}. of_int (N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) =
      e00 * y0 + e10 * y1 + e20 * y2 + e30 * y3 +
      (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-4)) * x $$ (m-h-1,0))"
  assumes y0_choice:
    "y0 =
      (if e00 = 1 then
        - (e10 * y1 + e20 * y2 + e30 * y3 +
           (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
           (∑h∈{m..<𝗏}. of_int (N $$ (h,m-4)) * x $$ (h,0))) / 2
       else
        (e10 * y1 + e20 * y2 + e30 * y3 +
         (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
         (∑h∈{m..<𝗏}. of_int (N $$ (h,m-4)) * x $$ (h,0))) / (1 - e00))"
  shows
    "y0^2 =
      ((∑h∈{0..<m}. of_int (N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
       (∑h∈{m..<𝗏}. of_int (N $$ (h,m-4)) * x $$ (h,0)))^2"
proof -
  let ?A =
    "e10 * y1 + e20 * y2 + e30 * y3 +
     (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
     (∑h∈{m..<𝗏}. of_int (N $$ (h,m-4)) * x $$ (h,0))"

  have Ltotal:
    "((∑h∈{0..<m}. of_int (N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
       (∑h∈{m..<𝗏}. of_int (N $$ (h,m-4)) * x $$ (h,0)))
     = e00 * y0 + ?A"
    using L0 by (simp add: algebra_simps)

  show ?thesis
  proof (cases "e00 = 1")
    case True
    then have y0_eq: "y0 = - ?A / 2"
      using y0_choice by simp

    have total_eq: "e00 * y0 + ?A = - y0"
      using True y0_eq
      by (simp add: field_simps)

    have "((∑h∈{0..<m}. of_int (N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
       (∑h∈{m..<𝗏}. of_int (N $$ (h,m-4)) * x $$ (h,0)))
      = - y0"
      using Ltotal total_eq by simp

    then show ?thesis
      by simp
  next
    case False
    then have y0_eq: "y0 = ?A / (1 - e00)"
      using y0_choice by simp
    then have "e00 * y0 + ?A = y0"
      using False
      by (simp add: field_simps)
    then show ?thesis
      using Ltotal by simp
  qed
qed

lemma induction_step_1_explicit:
  fixes e01 e11 e21 e31 :: rat
  fixes y0 y1 y2 y3 :: rat
  fixes x :: "rat mat"
  fixes m :: nat
  assumes L1:
    "(∑h∈{0..<m}. of_int (N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) =
      e01 * y0 + e11 * y1 + e21 * y2 + e31 * y3 +
      (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-3)) * x $$ (m-h-1,0))"
  assumes y1_choice:
    "y1 =
      (if e11 = 1 then
        - (e01 * y0 + e21 * y2 + e31 * y3 +
           (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
           (∑h∈{m..<𝗏}. of_int (N $$ (h,m-3)) * x $$ (h,0))) / 2
       else
        (e01 * y0 + e21 * y2 + e31 * y3 +
         (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
         (∑h∈{m..<𝗏}. of_int (N $$ (h,m-3)) * x $$ (h,0))) / (1 - e11))"
  shows
    "y1^2 =
      ((∑h∈{0..<m}. of_int (N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
       (∑h∈{m..<𝗏}. of_int (N $$ (h,m-3)) * x $$ (h,0)))^2"
proof -
  let ?A =
    "e01 * y0 + e21 * y2 + e31 * y3 +
     (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
     (∑h∈{m..<𝗏}. of_int (N $$ (h,m-3)) * x $$ (h,0))"

  have Ltotal:
    "((∑h∈{0..<m}. of_int (N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
       (∑h∈{m..<𝗏}. of_int (N $$ (h,m-3)) * x $$ (h,0)))
     = e11 * y1 + ?A"
    using L1 by (simp add: algebra_simps)

  show ?thesis
  proof (cases "e11 = 1")
    case True
    then have y1_eq: "y1 = - ?A / 2"
      using y1_choice by simp

    have total_eq: "e11 * y1 + ?A = - y1"
      using True y1_eq
      by (simp add: field_simps)

    have "((∑h∈{0..<m}. of_int (N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
       (∑h∈{m..<𝗏}. of_int (N $$ (h,m-3)) * x $$ (h,0)))
      = - y1"
      using Ltotal total_eq by simp

    then show ?thesis
      by simp
  next
    case False
    then have y1_eq: "y1 = ?A / (1 - e11)"
      using y1_choice by simp
    then have "e11 * y1 + ?A = y1"
      using False
      by (simp add: field_simps)
    then show ?thesis
      using Ltotal by simp
  qed
qed

lemma induction_step_2_explicit:
  fixes e02 e12 e22 e32 :: rat
  fixes y0 y1 y2 y3 :: rat
  fixes x :: "rat mat"
  fixes m :: nat
  assumes L2:
    "(∑h∈{0..<m}. of_int (N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) =
      e02 * y0 + e12 * y1 + e22 * y2 + e32 * y3 +
      (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-2)) * x $$ (m-h-1,0))"
  assumes y2_choice:
    "y2 =
      (if e22 = 1 then
        - (e02 * y0 + e12 * y1 + e32 * y3 +
           (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
           (∑h∈{m..<𝗏}. of_int (N $$ (h,m-2)) * x $$ (h,0))) / 2
       else
        (e02 * y0 + e12 * y1 + e32 * y3 +
         (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
         (∑h∈{m..<𝗏}. of_int (N $$ (h,m-2)) * x $$ (h,0))) / (1 - e22))"
  shows
    "y2^2 =
      ((∑h∈{0..<m}. of_int (N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
       (∑h∈{m..<𝗏}. of_int (N $$ (h,m-2)) * x $$ (h,0)))^2"
proof -
  let ?A =
    "e02 * y0 + e12 * y1 + e32 * y3 +
     (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
     (∑h∈{m..<𝗏}. of_int (N $$ (h,m-2)) * x $$ (h,0))"

  have Ltotal:
    "((∑h∈{0..<m}. of_int (N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
       (∑h∈{m..<𝗏}. of_int (N $$ (h,m-2)) * x $$ (h,0)))
     = e22 * y2 + ?A"
    using L2 by (simp add: algebra_simps)

  show ?thesis
  proof (cases "e22 = 1")
    case True
    then have y2_eq: "y2 = - ?A / 2"
      using y2_choice by simp

    have total_eq: "e22 * y2 + ?A = - y2"
      using True y2_eq
      by (simp add: field_simps)

    have "((∑h∈{0..<m}. of_int (N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
       (∑h∈{m..<𝗏}. of_int (N $$ (h,m-2)) * x $$ (h,0)))
      = - y2"
      using Ltotal total_eq by simp

    then show ?thesis
      by simp
  next
    case False
    then have y2_eq: "y2 = ?A / (1 - e22)"
      using y2_choice by simp
    then have "e22 * y2 + ?A = y2"
      using False
      by (simp add: field_simps)
    then show ?thesis
      using Ltotal by simp
  qed
qed

lemma induction_step_3_explicit:
  fixes e03 e13 e23 e33 :: rat
  fixes y0 y1 y2 y3 :: rat
  fixes x :: "rat mat"
  fixes m :: nat
  assumes L3:
    "(∑h∈{0..<m}. of_int (N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) =
      e03 * y0 + e13 * y1 + e23 * y2 + e33 * y3 +
      (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-1)) * x $$ (m-h-1,0))"
  assumes y3_choice:
    "y3 =
      (if e33 = 1 then
        - (e03 * y0 + e13 * y1 + e23 * y2 +
           (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
           (∑h∈{m..<𝗏}. of_int (N $$ (h,m-1)) * x $$ (h,0))) / 2
       else
        (e03 * y0 + e13 * y1 + e23 * y2 +
         (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
         (∑h∈{m..<𝗏}. of_int (N $$ (h,m-1)) * x $$ (h,0))) / (1 - e33))"
  shows
    "y3^2 =
      ((∑h∈{0..<m}. of_int (N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
       (∑h∈{m..<𝗏}. of_int (N $$ (h,m-1)) * x $$ (h,0)))^2"
proof -
  let ?A =
    "e03 * y0 + e13 * y1 + e23 * y2 +
     (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
     (∑h∈{m..<𝗏}. of_int (N $$ (h,m-1)) * x $$ (h,0))"

  have Ltotal:
    "((∑h∈{0..<m}. of_int (N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
       (∑h∈{m..<𝗏}. of_int (N $$ (h,m-1)) * x $$ (h,0)))
     = e33 * y3 + ?A"
    using L3 by (simp add: algebra_simps)

  show ?thesis
  proof (cases "e33 = 1")
    case True
    then have y3_eq: "y3 = - ?A / 2"
      using y3_choice by simp

    have total_eq: "e33 * y3 + ?A = - y3"
      using True y3_eq
      by (simp add: field_simps)

    have "((∑h∈{0..<m}. of_int (N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
       (∑h∈{m..<𝗏}. of_int (N $$ (h,m-1)) * x $$ (h,0)))
      = - y3"
      using Ltotal total_eq by simp

    then show ?thesis
      by simp
  next
    case False
    then have y3_eq: "y3 = ?A / (1 - e33)"
      using y3_choice by simp
    then have "e33 * y3 + ?A = y3"
      using False
      by (simp add: field_simps)
    then show ?thesis
      using Ltotal by simp
  qed
qed

lemma induction_step_0123_explicit:
  fixes e00 e10 e20 e30 e01 e11 e21 e31 e02 e12 e22 e32 e03 e13 e23 e33 :: rat
  fixes y0 y1 y2 y3 :: rat
  fixes x :: "rat mat"
  fixes m :: nat
  assumes L0:
    "(∑h∈{0..<m}. of_int (N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) =
      e00*y0 + e10*y1 + e20*y2 + e30*y3 +
      (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-4)) * x $$ (m-h-1,0))"
  assumes L1:
    "(∑h∈{0..<m}. of_int (N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) =
      e01*y0 + e11*y1 + e21*y2 + e31*y3 +
      (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-3)) * x $$ (m-h-1,0))"
  assumes L2:
    "(∑h∈{0..<m}. of_int (N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) =
      e02*y0 + e12*y1 + e22*y2 + e32*y3 +
      (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-2)) * x $$ (m-h-1,0))"
  assumes L3:
    "(∑h∈{0..<m}. of_int (N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) =
      e03*y0 + e13*y1 + e23*y2 + e33*y3 +
      (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-1)) * x $$ (m-h-1,0))"
  assumes y0_choice:
    "y0 =
      (if e00 = 1 then
        - (e10*y1 + e20*y2 + e30*y3 +
           (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
           (∑h∈{m..<𝗏}. of_int (N $$ (h,m-4)) * x $$ (h,0))) / 2
       else
        (e10*y1 + e20*y2 + e30*y3 +
         (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
         (∑h∈{m..<𝗏}. of_int (N $$ (h,m-4)) * x $$ (h,0))) / (1 - e00))"
  assumes y1_choice:
    "y1 =
      (if e11 = 1 then
        - (e01*y0 + e21*y2 + e31*y3 +
           (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
           (∑h∈{m..<𝗏}. of_int (N $$ (h,m-3)) * x $$ (h,0))) / 2
       else
        (e01*y0 + e21*y2 + e31*y3 +
         (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
         (∑h∈{m..<𝗏}. of_int (N $$ (h,m-3)) * x $$ (h,0))) / (1 - e11))"
  assumes y2_choice:
    "y2 =
      (if e22 = 1 then
        - (e02*y0 + e12*y1 + e32*y3 +
           (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
           (∑h∈{m..<𝗏}. of_int (N $$ (h,m-2)) * x $$ (h,0))) / 2
       else
        (e02*y0 + e12*y1 + e32*y3 +
         (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
         (∑h∈{m..<𝗏}. of_int (N $$ (h,m-2)) * x $$ (h,0))) / (1 - e22))"
  assumes y3_choice:
    "y3 =
      (if e33 = 1 then
        - (e03*y0 + e13*y1 + e23*y2 +
           (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
           (∑h∈{m..<𝗏}. of_int (N $$ (h,m-1)) * x $$ (h,0))) / 2
       else
        (e03*y0 + e13*y1 + e23*y2 +
         (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
         (∑h∈{m..<𝗏}. of_int (N $$ (h,m-1)) * x $$ (h,0))) / (1 - e33))"
  shows
    "y0^2 =
      ((∑h∈{0..<m}. of_int (N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
       (∑h∈{m..<𝗏}. of_int (N $$ (h,m-4)) * x $$ (h,0)))^2
    ∧ y1^2 =
      ((∑h∈{0..<m}. of_int (N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
       (∑h∈{m..<𝗏}. of_int (N $$ (h,m-3)) * x $$ (h,0)))^2
    ∧ y2^2 =
      ((∑h∈{0..<m}. of_int (N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
       (∑h∈{m..<𝗏}. of_int (N $$ (h,m-2)) * x $$ (h,0)))^2
    ∧ y3^2 =
      ((∑h∈{0..<m}. of_int (N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
       (∑h∈{m..<𝗏}. of_int (N $$ (h,m-1)) * x $$ (h,0)))^2"
  using induction_step_0_explicit[OF L0 y0_choice]
        induction_step_1_explicit[OF L1 y1_choice]
        induction_step_2_explicit[OF L2 y2_choice]
        induction_step_3_explicit[OF L3 y3_choice]
  by blast

lemma brc_v_eq_1:
  assumes v_eq_1: "𝗏 = 1"
  assumes four_sq: "a^2 + b^2 + c^2 + d^2 = 𝗄 - Λ"
  shows "∃x y z :: int. (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧
         of_int(x^2) = of_nat(𝗄 - Λ) * of_int(y^2) + of_nat Λ * of_int(z^2)"
proof -
  (* For v=1, construct a simple x vector *)
  define x :: "rat mat" where "x = mat 1 1 (λ(i,j). 1)"
  
  have x_val: "x $$ (0, 0) = 1"
    using x_def by simp
  
  (* Apply brc_x_equation *)
  have brc_v1: "(∑i ∈ {0..<1}. (∑h ∈ {0..<1}. of_int(N $$ (h,i)) * x $$ (h,0))^2) =
                of_int Λ * (∑j ∈ {0..<1}. x $$ (j,0))^2 + 
                of_int(𝗄 - Λ) * (∑j ∈ {0..<1}. (x $$ (j,0))^2)"
    using brc_x_equation[of x] v_eq_1 by simp
  
  (* Simplify the LHS: sum over {0..<1} has only one term at index 0 *)
  have lhs_simpl: "(∑i ∈ {0..<1}. (∑h ∈ {0..<1}. of_int(N $$ (h,i)) * x $$ (h,0))^2) = 
                   (of_int(N $$ (0,0)) * x $$ (0,0))^2"
    by simp
  then have lhs_val: "(∑i ∈ {0..<1}. (∑h ∈ {0..<1}. of_int(N $$ (h,i)) * x $$ (h,0))^2) = 
                      (of_int(N $$ (0,0)))^2"
    using x_val by simp
  
  (* Simplify the RHS *)
  have sum_x: "(∑j ∈ {0..<1}. x $$ (j,0)) = x $$ (0,0)"
    by simp
  then have sum_x_val: "(∑j ∈ {0..<1}. x $$ (j,0)) = 1"
    using x_val by simp
  
  have sum_x2: "(∑j ∈ {0..<1}. (x $$ (j,0))^2) = (x $$ (0,0))^2"
    by simp
  then have sum_x2_val: "(∑j ∈ {0..<1}. (x $$ (j,0))^2) = 1"
    using x_val by simp
  
  (* Combine *)
  have n00_eq: "(of_int(N $$ (0,0)) :: rat)^2 = of_int Λ + of_int(𝗄 - Λ)"
    using brc_v1 lhs_val sum_x_val sum_x2_val by auto
  
  have kl_sum: "of_nat Λ + of_nat(𝗄 - Λ) = (of_nat 𝗄 :: rat)"
    using blocksize_gt_index of_nat_diff by simp

  then have "(of_int(N $$ (0,0)))^2 = (of_int 𝗄 :: rat)"
  using n00_eq by simp
  
  have "of_int((N $$ (0,0))^2) = of_nat(𝗄 - Λ) * of_int(1^2) + of_nat Λ * of_int(1^2)"
  proof -
    have "(of_int(N $$ (0,0)) :: rat)^2 = (of_nat(𝗄 - Λ) :: rat) + (of_nat Λ :: rat)"
      using n00_eq kl_sum by simp
    then have "of_int((N $$ (0,0))^2) = (of_nat(𝗄 - Λ) :: rat) + (of_nat Λ :: rat)"
      by (simp add: power2_eq_square)
    also have "... = of_nat(𝗄 - Λ) * 1 + of_nat Λ * 1"
      by simp
    finally show ?thesis
      by (metis (mono_tags, lifting) mult.right_neutral of_int_eq_iff of_int_hom.hom_one 
        of_int_of_nat_eq of_nat_add one_power2)
  qed

  moreover have "(N $$ (0,0) ≠ 0 ∨ (1::int) ≠ 0 ∨ (1::int) ≠ 0)"
    by simp

  ultimately show ?thesis by blast
qed

definition S_of :: "rat mat ⇒ rat" where
  "S_of x = (∑i∈{0..<𝗏}. (∑h∈{0..<𝗏}. of_int (N $$ (h,i)) * x $$ (h,0))^2)"

definition t_of :: "rat mat ⇒ rat" where
  "t_of x = (∑j∈{0..<𝗏}. x $$ (j,0))"

definition u_of :: "rat mat ⇒ rat" where
  "u_of x = (∑j∈{0..<𝗏}. (x $$ (j,0))^2)"

lemma brc_x_equation_named:
  fixes x :: "rat mat"
  shows "S_of x = of_int (int Λ) * (t_of x)^2 + of_int (int (𝗄 - Λ)) * (u_of x)"
  unfolding S_of_def t_of_def u_of_def
  using brc_x_equation by simp

lemma brc_recursive_elimination_weak:
  fixes x :: "rat mat"
  assumes brc_eq: "(∑i∈{0..<𝗏}. (∑h∈{0..<𝗏}. of_int (N $$ (h,i)) * x $$ (h,0))^2)
                 = of_int (int Λ) * (∑j∈{0..<𝗏}. x $$ (j,0))^2
                 + of_int (int (𝗄 - Λ)) * (∑j∈{0..<𝗏}. (x $$ (j,0))^2)"
  shows "∃S t u :: rat.
           S = of_int (int Λ) * t^2 + of_int (int (𝗄 - Λ)) * u ∧
           t = (∑j∈{0..<𝗏}. x $$ (j,0)) ∧
           u = (∑j∈{0..<𝗏}. (x $$ (j,0))^2)"
  using brc_eq by (intro exI[of _ "(∑i∈{0..<𝗏}. (∑h∈{0..<𝗏}. of_int (N $$ (h,i)) * x $$ (h,0))^2)"]
                   exI[of _ "(∑j∈{0..<𝗏}. x $$ (j,0))"]
                   exI[of _ "(∑j∈{0..<𝗏}. (x $$ (j,0))^2)"]) simp

lemma sum_head4_from_tail:
  fixes f :: "nat ⇒ rat" and A :: rat and m :: nat
  assumes m4: "4 ≤ m"
  assumes eq: "(∑h = 0..<m. f h) = A + (∑h = 4..<m. f h)"
  shows "(∑h = 0..<4. f h) = A"
proof -
  have split: "(∑h = 0..<m. f h) = (∑h = 0..<4. f h) + (∑h = 4..<m. f h)"
    using m4 by (simp add: sum.atLeastLessThan_concat algebra_simps)
  from eq split show ?thesis by simp
qed

lemma brc_v_1_mod_4_identity:
  fixes a b c d m :: nat
  fixes x0 x1 x2 x3 :: rat
  assumes four_sq: "a^2 + b^2 + c^2 + d^2 = 𝗄 - Λ"
  assumes m_props: "m > 3" "𝗏 ≥ m"
  defines "x ≡ mat 𝗏 1 (λ(i,j).
    if j = 0 then
      (if i = m - 4 then x0
       else if i = m - 3 then x1
       else if i = m - 2 then x2
       else if i = m - 1 then x3
       else 0)
    else 0)"
  shows
   "(∑i∈{0..<𝗏}. (∑h∈{0..<𝗏}. of_int (N $$ (h,i)) * x $$ (h,0))^2)
    =
    of_int (int Λ) * (x0 + x1 + x2 + x3)^2
    + of_int (int (𝗄 - Λ)) * (x0^2 + x1^2 + x2^2 + x3^2)"
proof -
  have m4: "4 ≤ m"
    using m_props by simp

  let ?S = "{m - 4, m - 3, m - 2, m - 1}"

  have S_subset: "?S ⊆ {0..<𝗏}"
    using m_props m4 by auto

  have dists:
    "m - 4 ≠ m - 3"
    "m - 4 ≠ m - 2"
    "m - 4 ≠ m - 1"
    "m - 3 ≠ m - 2"
    "m - 3 ≠ m - 1"
    "m - 2 ≠ m - 1"
    using m4 by auto

  have xm4: "x $$ (m - 4,0) = x0"
    unfolding x_def using m_props m4 by simp

  have xm3: "x $$ (m - 3,0) = x1"
    unfolding x_def using m_props m4 by auto

  have xm2: "x $$ (m - 2,0) = x2"
    unfolding x_def using m_props m4 by auto

  have xm1: "x $$ (m - 1,0) = x3"
    unfolding x_def using m_props m4 by auto

  have outside_zero:
    "j ∈ {0..<𝗏} ⟹ j ∉ ?S ⟹ x $$ (j,0) = 0" for j
    unfolding x_def using m_props by auto

  have sum_all:
    "(∑j∈{0..<𝗏}. x $$ (j,0)) = x0 + x1 + x2 + x3"
  proof -
    have "(∑j∈{0..<𝗏}. x $$ (j,0)) = (∑j∈?S. x $$ (j,0))"
      by (rule sum.mono_neutral_cong_right) (use S_subset outside_zero in auto)
    also have "... = x0 + x1 + x2 + x3"
      using xm4 xm3 xm2 xm1 dists by simp
    finally show ?thesis .
  qed

  have sumsq_all:
    "(∑j∈{0..<𝗏}. (x $$ (j,0))^2) = x0^2 + x1^2 + x2^2 + x3^2"
  proof -
    have "(∑j∈{0..<𝗏}. (x $$ (j,0))^2) = (∑j∈?S. (x $$ (j,0))^2)"
      by (rule sum.mono_neutral_cong_right) (use S_subset outside_zero in auto)
    also have "... = x0^2 + x1^2 + x2^2 + x3^2"
      using xm4 xm3 xm2 xm1 dists by simp
    finally show ?thesis .
  qed

  show ?thesis
    using brc_x_equation[of x] sum_all sumsq_all
    by simp
qed

lemma y_of_norm:
  fixes a b c d :: nat
  fixes x0 x1 x2 x3 :: rat
  shows
   "let y = y_of ((a,b,c,d),(x0,x1,x2,x3)) in
      one_of y ^ 2 + two_of y ^ 2 + three_of y ^ 2 + four_of y ^ 2
      =
      of_nat (a^2 + b^2 + c^2 + d^2) *
      (x0^2 + x1^2 + x2^2 + x3^2)"
  by (simp add: algebra_simps power2_eq_square)

lemma y_of_norm_brc:
  fixes a b c d :: nat
  fixes x0 x1 x2 x3 :: rat
  assumes four_sq: "a^2 + b^2 + c^2 + d^2 = 𝗄 - Λ"
  shows
   "let y = y_of ((a,b,c,d),(x0,x1,x2,x3)) in
      one_of y ^ 2 + two_of y ^ 2 + three_of y ^ 2 + four_of y ^ 2
      =
      of_nat (𝗄 - Λ) *
      (x0^2 + x1^2 + x2^2 + x3^2)"
  using y_of_norm[of a b c d x0 x1 x2 x3] four_sq
  by simp

lemma brc_four_variable_substitution:
  fixes a b c d :: nat
  fixes x0 x1 x2 x3 :: rat
  assumes four_sq: "a^2 + b^2 + c^2 + d^2 = 𝗄 - Λ"
  defines "y ≡ y_of ((a,b,c,d),(x0,x1,x2,x3))"
  shows
   "of_int (int Λ) * (x0 + x1 + x2 + x3)^2
    + of_int (int (𝗄 - Λ)) * (x0^2 + x1^2 + x2^2 + x3^2)
    =
    of_int (int Λ) * (x0 + x1 + x2 + x3)^2
    + one_of y^2 + two_of y^2 + three_of y^2 + four_of y^2"
proof -
  have norm:
    "one_of y^2 + two_of y^2 + three_of y^2 + four_of y^2
     =
     of_nat (𝗄 - Λ) * (x0^2 + x1^2 + x2^2 + x3^2)"
    unfolding y_def
    using y_of_norm_brc[OF four_sq, of x0 x1 x2 x3]
    by simp
  show ?thesis
    using norm by simp
qed

lemma brc_v_1_mod_4_y_identity:
  fixes a b c d m :: nat
  fixes x0 x1 x2 x3 :: rat
  assumes four_sq: "a^2 + b^2 + c^2 + d^2 = 𝗄 - Λ"
  assumes m_props: "m > 3" "𝗏 ≥ m"
  defines "y ≡ y_of ((a,b,c,d),(x0,x1,x2,x3))"
  shows
   "(∑i∈{0..<𝗏}. (∑h∈{0..<𝗏}. of_int (N $$ (h,i)) *
      (mat 𝗏 1 (λ(i,j).
        if j = 0 then
          (if i = m - 4 then x0
           else if i = m - 3 then x1
           else if i = m - 2 then x2
           else if i = m - 1 then x3
           else 0)
        else 0)) $$ (h,0))^2)
    =
    of_int (int Λ) * (x0 + x1 + x2 + x3)^2
    + one_of y^2 + two_of y^2 + three_of y^2 + four_of y^2"
  using brc_v_1_mod_4_identity[OF four_sq m_props]
        brc_four_variable_substitution[OF four_sq, of x0 x1 x2 x3]
  unfolding y_def
  by simp

lemma brc_v_1_mod_4_y_identity_inv:
  fixes a b c d m :: nat
  fixes y0 y1 y2 y3 :: rat
  assumes four_sq: "a^2 + b^2 + c^2 + d^2 = 𝗄 - Λ"
  assumes m_props: "m > 3" "𝗏 ≥ m"
  defines "xs ≡ y_inv_of ((a,b,c,d),(y0,y1,y2,y3))"
  shows
   "(∑i∈{0..<𝗏}. (∑h∈{0..<𝗏}. of_int (N $$ (h,i)) *
      (mat 𝗏 1 (λ(i,j).
        if j = 0 then
          (if i = m - 4 then one_of xs
           else if i = m - 3 then two_of xs
           else if i = m - 2 then three_of xs
           else if i = m - 1 then four_of xs
           else 0)
        else 0)) $$ (h,0))^2)
    =
    of_int (int Λ) *
      (one_of xs + two_of xs + three_of xs + four_of xs)^2
    + y0^2 + y1^2 + y2^2 + y3^2"
proof -
  have nz: "a^2 + b^2 + c^2 + d^2 ≠ 0"
    using four_sq blocksize_gt_index by simp

  have yback:
    "y_of ((a,b,c,d), xs) = (y0,y1,y2,y3)"
    unfolding xs_def
    using y_inverses_part_2[OF nz, of y0 y1 y2 y3]
    by simp

  have norm:
    "of_nat (𝗄 - Λ) *
      (one_of xs^2 + two_of xs^2 + three_of xs^2 + four_of xs^2)
     =
     y0^2 + y1^2 + y2^2 + y3^2"
  proof -
    have norm0:
      "let y = y_of ((a,b,c,d),
          (one_of xs, two_of xs, three_of xs, four_of xs)) in
        one_of y ^ 2 + two_of y ^ 2 + three_of y ^ 2 + four_of y ^ 2
        =
        of_nat (𝗄 - Λ) *
        (one_of xs^2 + two_of xs^2 + three_of xs^2 + four_of xs^2)"
      using y_of_norm_brc[OF four_sq,
        of "one_of xs" "two_of xs" "three_of xs" "four_of xs"]
      by simp

    have tuple_xs:
      "(one_of xs, two_of xs, three_of xs, four_of xs) = xs"
      by (cases xs) simp

    have norm1:
      "one_of (y_of ((a,b,c,d), xs))^2
      + two_of (y_of ((a,b,c,d), xs))^2
      + three_of (y_of ((a,b,c,d), xs))^2
      + four_of (y_of ((a,b,c,d), xs))^2
      =
      of_nat (𝗄 - Λ) *
        (one_of xs^2 + two_of xs^2 + three_of xs^2 + four_of xs^2)"
      using norm0 tuple_xs
      by (simp add: Let_def)

    have "of_nat (𝗄 - Λ) *
        (one_of xs^2 + two_of xs^2 + three_of xs^2 + four_of xs^2)
      =
      one_of (y_of ((a,b,c,d), xs))^2
      + two_of (y_of ((a,b,c,d), xs))^2
      + three_of (y_of ((a,b,c,d), xs))^2
      + four_of (y_of ((a,b,c,d), xs))^2"
      using norm1 by simp

    also have "... = y0^2 + y1^2 + y2^2 + y3^2"
      using yback by simp

    finally show ?thesis .
  qed

  have base:
   "(∑i∈{0..<𝗏}. (∑h∈{0..<𝗏}. of_int (N $$ (h,i)) *
      (mat 𝗏 1 (λ(i,j).
        if j = 0 then
          (if i = m - 4 then one_of xs
           else if i = m - 3 then two_of xs
           else if i = m - 2 then three_of xs
           else if i = m - 1 then four_of xs
           else 0)
        else 0)) $$ (h,0))^2)
    =
    of_int (int Λ) *
      (one_of xs + two_of xs + three_of xs + four_of xs)^2
    + of_int (int (𝗄 - Λ)) *
      (one_of xs^2 + two_of xs^2 + three_of xs^2 + four_of xs^2)"
    using brc_v_1_mod_4_identity[
      OF four_sq m_props,
      of "one_of xs" "two_of xs" "three_of xs" "four_of xs"]
    by simp

  show ?thesis
    using base norm by simp
qed

lemma brc_last_four_Li_linear_combinations:
  fixes a b c d m :: nat
  fixes x :: "rat mat"
  fixes y0' y1' y2' y3' :: rat
  fixes x0 x1 x2 x3 :: rat
  assumes four_sq: "a^2 + b^2 + c^2 + d^2 = 𝗄 - Λ"
  assumes m_v: "𝗏 ≥ m"
  assumes m_gt3: "m > 3"
  assumes x0_def: "x0 = x $$ (m - 4, 0)"
  assumes x1_def: "x1 = x $$ (m - 3, 0)"
  assumes x2_def: "x2 = x $$ (m - 2, 0)"
  assumes x3_def: "x3 = x $$ (m - 1, 0)"
  assumes x0_eq: "x0 = one_of (y_inv_of ((a,b,c,d),(y0',y1',y2',y3')))"
  assumes x1_eq: "x1 = two_of (y_inv_of ((a,b,c,d),(y0',y1',y2',y3')))"
  assumes x2_eq: "x2 = three_of (y_inv_of ((a,b,c,d),(y0',y1',y2',y3')))"
  assumes x3_eq: "x3 = four_of (y_inv_of ((a,b,c,d),(y0',y1',y2',y3')))"
  shows
   "∃c00 c10 c20 c30 c01 c11 c21 c31 c02 c12 c22 c32 c03 c13 c23 c33.
      (∑h = 0..<m. rat_of_int (N $$ (m - h - 1, m - 4)) * x $$ (m - h - 1, 0)) =
        c00*y0' + c10*y1' + c20*y2' + c30*y3' +
        (∑h = 4..<m. rat_of_int (N $$ (m - h - 1, m - 4)) * x $$ (m - h - 1, 0))
    ∧ (∑h = 0..<m. rat_of_int (N $$ (m - h - 1, m - 3)) * x $$ (m - h - 1, 0)) =
        c01*y0' + c11*y1' + c21*y2' + c31*y3' +
        (∑h = 4..<m. rat_of_int (N $$ (m - h - 1, m - 3)) * x $$ (m - h - 1, 0))
    ∧ (∑h = 0..<m. rat_of_int (N $$ (m - h - 1, m - 2)) * x $$ (m - h - 1, 0)) =
        c02*y0' + c12*y1' + c22*y2' + c32*y3' +
        (∑h = 4..<m. rat_of_int (N $$ (m - h - 1, m - 2)) * x $$ (m - h - 1, 0))
    ∧ (∑h = 0..<m. rat_of_int (N $$ (m - h - 1, m - 1)) * x $$ (m - h - 1, 0)) =
        c03*y0' + c13*y1' + c23*y2' + c33*y3' +
        (∑h = 4..<m. rat_of_int (N $$ (m - h - 1, m - 1)) * x $$ (m - h - 1, 0))"
proof -
  have i0_in: "(0::nat) ∈ {0..<4}" by simp
  have i1_in: "(1::nat) ∈ {0..<4}" by simp
  have i2_in: "(2::nat) ∈ {0..<4}" by simp
  have i3_in: "(3::nat) ∈ {0..<4}" by simp

  obtain c00 c10 c20 c30 where Li_m4:
    "(∑h = 0..<m. rat_of_int (N $$ (m - h - 1, m - 4)) * x $$ (m - h - 1, 0)) =
    c00*y0' + c10*y1' + c20*y2' + c30*y3' +
    (∑h = 4..<m. rat_of_int (N $$ (m - h - 1, m - 4)) * x $$ (m - h - 1, 0))"
  proof -
    obtain e0 e1 e2 e3 where e:
      "(∑h = 0..<m. rat_of_int (N $$ (m - h - 1, m - 3 - 1)) * x $$ (m - h - 1, 0)) =
      e0 * y0' + e1 * y1' + e2 * y2' + e3 * y3' +
      (∑h = 4..<m. rat_of_int (N $$ (m - h - 1, m - 3 - 1)) * x $$ (m - h - 1, 0))"
      using linear_comb_of_y_part_2[
          OF four_sq m_v m_gt3 i3_in
          x0_def x1_def x2_def x3_def
          x0_eq x1_eq x2_eq x3_eq]
      by blast

    have simp_col: "m - 3 - 1 = m - 4"
      using m_gt3 by simp

    show ?thesis
      using e simp_col that by simp
  qed

  obtain c01 c11 c21 c31 where Li_m3:
    "(∑h = 0..<m. rat_of_int (N $$ (m - h - 1, m - 3)) * x $$ (m - h - 1, 0)) =
    c01*y0' + c11*y1' + c21*y2' + c31*y3' +
    (∑h = 4..<m. rat_of_int (N $$ (m - h - 1, m - 3)) * x $$ (m - h - 1, 0))"
  proof -
    obtain e0 e1 e2 e3 where e:
      "(∑h = 0..<m. rat_of_int (N $$ (m - h - 1, m - 2 - 1)) * x $$ (m - h - 1, 0)) =
      e0 * y0' + e1 * y1' + e2 * y2' + e3 * y3' +
      (∑h = 4..<m. rat_of_int (N $$ (m - h - 1, m - 2 - 1)) * x $$ (m - h - 1, 0))"
      using linear_comb_of_y_part_2[
          OF four_sq m_v m_gt3 i2_in
         x0_def x1_def x2_def x3_def
         x0_eq x1_eq x2_eq x3_eq]
      by blast

    have simp_col: "m - 2 - 1 = m - 3"
      using m_gt3 by simp

    show ?thesis
      using e simp_col that by simp
  qed

  obtain c02 c12 c22 c32 where Li_m2:
    "(∑h = 0..<m. rat_of_int (N $$ (m - h - 1, m - 2)) * x $$ (m - h - 1, 0)) =
    c02*y0' + c12*y1' + c22*y2' + c32*y3' +
    (∑h = 4..<m. rat_of_int (N $$ (m - h - 1, m - 2)) * x $$ (m - h - 1, 0))"
  proof -
    obtain e0 e1 e2 e3 where e:
      "(∑h = 0..<m. rat_of_int (N $$ (m - h - 1, m - 1 - 1)) * x $$ (m - h - 1, 0)) =
      e0 * y0' + e1 * y1' + e2 * y2' + e3 * y3' +
      (∑h = 4..<m. rat_of_int (N $$ (m - h - 1, m - 1 - 1)) * x $$ (m - h - 1, 0))"
      using linear_comb_of_y_part_2[
          OF four_sq m_v m_gt3 i1_in
         x0_def x1_def x2_def x3_def
         x0_eq x1_eq x2_eq x3_eq]
      by blast

    have simp_col: "m - 1 - 1 = m - 2"
      using m_gt3 by simp

    show ?thesis
      using e simp_col that by simp
  qed

  obtain c03 c13 c23 c33 where Li_m1:
    "(∑h = 0..<m. rat_of_int (N $$ (m - h - 1, m - 1)) * x $$ (m - h - 1, 0)) =
    c03*y0' + c13*y1' + c23*y2' + c33*y3' +
    (∑h = 4..<m. rat_of_int (N $$ (m - h - 1, m - 1)) * x $$ (m - h - 1, 0))"
  proof -
    obtain e0 e1 e2 e3 where e:
      "(∑h = 0..<m. rat_of_int (N $$ (m - h - 1, m - 0 - 1)) * x $$ (m - h - 1, 0)) =
      e0 * y0' + e1 * y1' + e2 * y2' + e3 * y3' +
     (∑h = 4..<m. rat_of_int (N $$ (m - h - 1, m - 0 - 1)) * x $$ (m - h - 1, 0))"
      using linear_comb_of_y_part_2[
          OF four_sq m_v m_gt3 i0_in
          x0_def x1_def x2_def x3_def
          x0_eq x1_eq x2_eq x3_eq]
      by blast

    have simp_col: "m - 0 - 1 = m - 1"
      using m_gt3 by simp

    show ?thesis
      using e simp_col that by simp
  qed

  show ?thesis
    using Li_m4 Li_m3 Li_m2 Li_m1 by blast
qed

lemma brc_last_four_Ls_linear_combinations:
  fixes a b c d m :: nat
  fixes x :: "rat mat"
  fixes y0' y1' y2' y3' :: rat
  fixes x0 x1 x2 x3 :: rat
  assumes four_sq: "a^2 + b^2 + c^2 + d^2 = 𝗄 - Λ"
  assumes m_v: "𝗏 ≥ m"
  assumes m_gt3: "m > 3"
  assumes x0_def: "x0 = x $$ (m - 4, 0)"
  assumes x1_def: "x1 = x $$ (m - 3, 0)"
  assumes x2_def: "x2 = x $$ (m - 2, 0)"
  assumes x3_def: "x3 = x $$ (m - 1, 0)"
  assumes x0_eq: "x0 = one_of (y_inv_of ((a,b,c,d),(y0',y1',y2',y3')))"
  assumes x1_eq: "x1 = two_of (y_inv_of ((a,b,c,d),(y0',y1',y2',y3')))"
  assumes x2_eq: "x2 = three_of (y_inv_of ((a,b,c,d),(y0',y1',y2',y3')))"
  assumes x3_eq: "x3 = four_of (y_inv_of ((a,b,c,d),(y0',y1',y2',y3')))"
  defines "L0 ≡
      (∑h = 0..<m. rat_of_int (N $$ (m - h - 1, m - 4)) * x $$ (m - h - 1, 0))
    + (∑h = m..<𝗏. rat_of_int (N $$ (h, m - 4)) * x $$ (h, 0))"
  defines "L1 ≡
      (∑h = 0..<m. rat_of_int (N $$ (m - h - 1, m - 3)) * x $$ (m - h - 1, 0))
    + (∑h = m..<𝗏. rat_of_int (N $$ (h, m - 3)) * x $$ (h, 0))"
  defines "L2 ≡
      (∑h = 0..<m. rat_of_int (N $$ (m - h - 1, m - 2)) * x $$ (m - h - 1, 0))
    + (∑h = m..<𝗏. rat_of_int (N $$ (h, m - 2)) * x $$ (h, 0))"
  defines "L3 ≡
      (∑h = 0..<m. rat_of_int (N $$ (m - h - 1, m - 1)) * x $$ (m - h - 1, 0))
    + (∑h = m..<𝗏. rat_of_int (N $$ (h, m - 1)) * x $$ (h, 0))"
  shows
   "∃c00 c10 c20 c30 c01 c11 c21 c31 c02 c12 c22 c32 c03 c13 c23 c33.
      L0 =
        c00*y0' + c10*y1' + c20*y2' + c30*y3'
        + (∑h = 4..<m. rat_of_int (N $$ (m - h - 1, m - 4)) * x $$ (m - h - 1, 0))
        + (∑h = m..<𝗏. rat_of_int (N $$ (h, m - 4)) * x $$ (h, 0))
    ∧ L1 =
        c01*y0' + c11*y1' + c21*y2' + c31*y3'
        + (∑h = 4..<m. rat_of_int (N $$ (m - h - 1, m - 3)) * x $$ (m - h - 1, 0))
        + (∑h = m..<𝗏. rat_of_int (N $$ (h, m - 3)) * x $$ (h, 0))
    ∧ L2 =
        c02*y0' + c12*y1' + c22*y2' + c32*y3'
        + (∑h = 4..<m. rat_of_int (N $$ (m - h - 1, m - 2)) * x $$ (m - h - 1, 0))
        + (∑h = m..<𝗏. rat_of_int (N $$ (h, m - 2)) * x $$ (h, 0))
    ∧ L3 =
        c03*y0' + c13*y1' + c23*y2' + c33*y3'
        + (∑h = 4..<m. rat_of_int (N $$ (m - h - 1, m - 1)) * x $$ (m - h - 1, 0))
        + (∑h = m..<𝗏. rat_of_int (N $$ (h, m - 1)) * x $$ (h, 0))"
proof -
  obtain c00 c10 c20 c30 c01 c11 c21 c31 c02 c12 c22 c32 c03 c13 c23 c33
    where coeffs:
      "(∑h = 0..<m. rat_of_int (N $$ (m - h - 1, m - 4)) * x $$ (m - h - 1, 0)) =
        c00*y0' + c10*y1' + c20*y2' + c30*y3' +
        (∑h = 4..<m. rat_of_int (N $$ (m - h - 1, m - 4)) * x $$ (m - h - 1, 0))"
      "(∑h = 0..<m. rat_of_int (N $$ (m - h - 1, m - 3)) * x $$ (m - h - 1, 0)) =
        c01*y0' + c11*y1' + c21*y2' + c31*y3' +
        (∑h = 4..<m. rat_of_int (N $$ (m - h - 1, m - 3)) * x $$ (m - h - 1, 0))"
      "(∑h = 0..<m. rat_of_int (N $$ (m - h - 1, m - 2)) * x $$ (m - h - 1, 0)) =
        c02*y0' + c12*y1' + c22*y2' + c32*y3' +
        (∑h = 4..<m. rat_of_int (N $$ (m - h - 1, m - 2)) * x $$ (m - h - 1, 0))"
      "(∑h = 0..<m. rat_of_int (N $$ (m - h - 1, m - 1)) * x $$ (m - h - 1, 0)) =
        c03*y0' + c13*y1' + c23*y2' + c33*y3' +
        (∑h = 4..<m. rat_of_int (N $$ (m - h - 1, m - 1)) * x $$ (m - h - 1, 0))"
    using brc_last_four_Li_linear_combinations[
      OF four_sq m_v m_gt3
         x0_def x1_def x2_def x3_def
         x0_eq x1_eq x2_eq x3_eq]
    by blast

  show ?thesis
  proof (intro exI conjI)
    show "L0 =
        c00*y0' + c10*y1' + c20*y2' + c30*y3'
        + (∑h = 4..<m. rat_of_int (N $$ (m - h - 1, m - 4)) * x $$ (m - h - 1, 0))
        + (∑h = m..<𝗏. rat_of_int (N $$ (h, m - 4)) * x $$ (h, 0))"
      unfolding L0_def
      using coeffs(1)
      by simp

    show "L1 =
        c01*y0' + c11*y1' + c21*y2' + c31*y3'
        + (∑h = 4..<m. rat_of_int (N $$ (m - h - 1, m - 3)) * x $$ (m - h - 1, 0))
        + (∑h = m..<𝗏. rat_of_int (N $$ (h, m - 3)) * x $$ (h, 0))"
      unfolding L1_def
      using coeffs(2)
      by simp

    show "L2 =
        c02*y0' + c12*y1' + c22*y2' + c32*y3'
        + (∑h = 4..<m. rat_of_int (N $$ (m - h - 1, m - 2)) * x $$ (m - h - 1, 0))
        + (∑h = m..<𝗏. rat_of_int (N $$ (h, m - 2)) * x $$ (h, 0))"
      unfolding L2_def
      using coeffs(3)
      by simp

    show "L3 =
        c03*y0' + c13*y1' + c23*y2' + c33*y3'
        + (∑h = 4..<m. rat_of_int (N $$ (m - h - 1, m - 1)) * x $$ (m - h - 1, 0))
        + (∑h = m..<𝗏. rat_of_int (N $$ (h, m - 1)) * x $$ (h, 0))"
      unfolding L3_def
      using coeffs(4)
      by simp
  qed
qed

lemma brc_L0_from_last_four:
  fixes a b c d m :: nat
  fixes x :: "rat mat"
  fixes y0 y1 y2 y3 :: rat
  fixes x0 x1 x2 x3 :: rat
  assumes four_sq: "a^2 + b^2 + c^2 + d^2 = 𝗄 - Λ"
  assumes m_v: "𝗏 ≥ m"
  assumes m_gt3: "m > 3"
  assumes x0_def: "x0 = x $$ (m - 4, 0)"
  assumes x1_def: "x1 = x $$ (m - 3, 0)"
  assumes x2_def: "x2 = x $$ (m - 2, 0)"
  assumes x3_def: "x3 = x $$ (m - 1, 0)"
  assumes x0_eq: "x0 = one_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x1_eq: "x1 = two_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x2_eq: "x2 = three_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x3_eq: "x3 = four_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  shows
    "∃c00 c10 c20 c30.
      (∑h = 0..<m. of_int (N $$ (m - h - 1, m - 4)) * x $$ (m - h - 1, 0)) =
        c00*y0 + c10*y1 + c20*y2 + c30*y3 +
        (∑h = 4..<m. of_int (N $$ (m - h - 1, m - 4)) * x $$ (m - h - 1, 0))"
proof -
  have i3_in: "(3::nat) ∈ {0..<4}" by simp

  obtain c00 c10 c20 c30 where coeff:
    "(∑h = 0..<m. of_int (N $$ (m - h - 1, m - 4)) * x $$ (m - h - 1, 0)) =
      c00*y0 + c10*y1 + c20*y2 + c30*y3 +
      (∑h = 4..<m. of_int (N $$ (m - h - 1, m - 4)) * x $$ (m - h - 1, 0))"
  proof -
    obtain e0 e1 e2 e3 where e:
      "(∑h = 0..<m. of_int (N $$ (m - h - 1, m - 3 - 1)) * x $$ (m - h - 1, 0)) =
       e0*y0 + e1*y1 + e2*y2 + e3*y3 +
       (∑h = 4..<m. of_int (N $$ (m - h - 1, m - 3 - 1)) * x $$ (m - h - 1, 0))"
      using linear_comb_of_y_part_2[
        OF four_sq m_v m_gt3 i3_in
           x0_def x1_def x2_def x3_def
           x0_eq x1_eq x2_eq x3_eq]
      by blast

    have simp_col: "m - 3 - 1 = m - 4"
      using m_gt3 by simp

    show ?thesis
      using e simp_col that by simp
  qed

  show ?thesis
    using coeff by blast
qed

lemma brc_L1_from_last_four:
  fixes a b c d m :: nat
  fixes x :: "rat mat"
  fixes y0 y1 y2 y3 :: rat
  fixes x0 x1 x2 x3 :: rat
  assumes four_sq: "a^2 + b^2 + c^2 + d^2 = 𝗄 - Λ"
  assumes m_v: "𝗏 ≥ m"
  assumes m_gt3: "m > 3"
  assumes x0_def: "x0 = x $$ (m - 4, 0)"
  assumes x1_def: "x1 = x $$ (m - 3, 0)"
  assumes x2_def: "x2 = x $$ (m - 2, 0)"
  assumes x3_def: "x3 = x $$ (m - 1, 0)"
  assumes x0_eq: "x0 = one_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x1_eq: "x1 = two_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x2_eq: "x2 = three_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x3_eq: "x3 = four_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  shows
    "∃c01 c11 c21 c31.
      (∑h = 0..<m. of_int (N $$ (m - h - 1, m - 3)) * x $$ (m - h - 1, 0)) =
        c01*y0 + c11*y1 + c21*y2 + c31*y3 +
        (∑h = 4..<m. of_int (N $$ (m - h - 1, m - 3)) * x $$ (m - h - 1, 0))"
proof -
  have i2_in: "(2::nat) ∈ {0..<4}" by simp

  obtain c01 c11 c21 c31 where coeff:
    "(∑h = 0..<m. of_int (N $$ (m - h - 1, m - 3)) * x $$ (m - h - 1, 0)) =
      c01*y0 + c11*y1 + c21*y2 + c31*y3 +
      (∑h = 4..<m. of_int (N $$ (m - h - 1, m - 3)) * x $$ (m - h - 1, 0))"
  proof -
    obtain e0 e1 e2 e3 where e:
      "(∑h = 0..<m. of_int (N $$ (m - h - 1, m - 2 - 1)) * x $$ (m - h - 1, 0)) =
       e0*y0 + e1*y1 + e2*y2 + e3*y3 +
       (∑h = 4..<m. of_int (N $$ (m - h - 1, m - 2 - 1)) * x $$ (m - h - 1, 0))"
      using linear_comb_of_y_part_2[
        OF four_sq m_v m_gt3 i2_in
           x0_def x1_def x2_def x3_def
           x0_eq x1_eq x2_eq x3_eq]
      by blast

    have simp_col: "m - 2 - 1 = m - 3"
      using m_gt3 by simp

    show ?thesis
      using e simp_col that by simp
  qed

  show ?thesis
    using coeff by blast
qed

lemma brc_L2_from_last_four:
  fixes a b c d m :: nat
  fixes x :: "rat mat"
  fixes y0 y1 y2 y3 :: rat
  fixes x0 x1 x2 x3 :: rat
  assumes four_sq: "a^2 + b^2 + c^2 + d^2 = 𝗄 - Λ"
  assumes m_v: "𝗏 ≥ m"
  assumes m_gt3: "m > 3"
  assumes x0_def: "x0 = x $$ (m - 4, 0)"
  assumes x1_def: "x1 = x $$ (m - 3, 0)"
  assumes x2_def: "x2 = x $$ (m - 2, 0)"
  assumes x3_def: "x3 = x $$ (m - 1, 0)"
  assumes x0_eq: "x0 = one_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x1_eq: "x1 = two_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x2_eq: "x2 = three_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x3_eq: "x3 = four_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  shows
    "∃c02 c12 c22 c32.
    (∑h = 0..<m. of_int (N $$ (m - h - 1, m - 2)) * x $$ (m - h - 1, 0)) =
      c02*y0 + c12*y1 + c22*y2 + c32*y3 +
      (∑h = 4..<m. of_int (N $$ (m - h - 1, m - 2)) * x $$ (m - h - 1, 0))"
proof -
  have i1_in: "(1::nat) ∈ {0..<4}" by simp

  obtain c02 c12 c22 c32 where coeff:
    "(∑h = 0..<m. of_int (N $$ (m - h - 1, m - 2)) * x $$ (m - h - 1, 0)) =
      c02*y0 + c12*y1 + c22*y2 + c32*y3 +
      (∑h = 4..<m. of_int (N $$ (m - h - 1, m - 2)) * x $$ (m - h - 1, 0))"
  proof -
    obtain e0 e1 e2 e3 where e:
      "(∑h = 0..<m. of_int (N $$ (m - h - 1, m - 1 - 1)) * x $$ (m - h - 1, 0)) =
       e0*y0 + e1*y1 + e2*y2 + e3*y3 +
       (∑h = 4..<m. of_int (N $$ (m - h - 1, m - 1 - 1)) * x $$ (m - h - 1, 0))"
      using linear_comb_of_y_part_2[
        OF four_sq m_v m_gt3 i1_in
           x0_def x1_def x2_def x3_def
           x0_eq x1_eq x2_eq x3_eq]
      by blast

    have simp_col: "m - 1 - 1 = m - 2"
      using m_gt3 by simp

    show ?thesis
      using e simp_col that by simp
  qed

  show ?thesis
    using coeff by blast
qed

lemma brc_L3_from_last_four:
  fixes a b c d m :: nat
  fixes x :: "rat mat"
  fixes y0 y1 y2 y3 :: rat
  fixes x0 x1 x2 x3 :: rat
  assumes four_sq: "a^2 + b^2 + c^2 + d^2 = 𝗄 - Λ"
  assumes m_v: "𝗏 ≥ m"
  assumes m_gt3: "m > 3"
  assumes x0_def: "x0 = x $$ (m - 4, 0)"
  assumes x1_def: "x1 = x $$ (m - 3, 0)"
  assumes x2_def: "x2 = x $$ (m - 2, 0)"
  assumes x3_def: "x3 = x $$ (m - 1, 0)"
  assumes x0_eq: "x0 = one_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x1_eq: "x1 = two_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x2_eq: "x2 = three_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x3_eq: "x3 = four_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
shows
  "∃c03 c13 c23 c33.
    (∑h = 0..<m. of_int (N $$ (m - h - 1, m - 1)) * x $$ (m - h - 1, 0)) =
      c03*y0 + c13*y1 + c23*y2 + c33*y3 +
      (∑h = 4..<m. of_int (N $$ (m - h - 1, m - 1)) * x $$ (m - h - 1, 0))"
proof -
  have i0_in: "(0::nat) ∈ {0..<4}" by simp

  obtain c03 c13 c23 c33 where coeff:
    "(∑h = 0..<m. of_int (N $$ (m - h - 1, m - 1)) * x $$ (m - h - 1, 0)) =
      c03*y0 + c13*y1 + c23*y2 + c33*y3 +
      (∑h = 4..<m. of_int (N $$ (m - h - 1, m - 1)) * x $$ (m - h - 1, 0))"
  proof -
    obtain e0 e1 e2 e3 where e:
      "(∑h = 0..<m. of_int (N $$ (m - h - 1, m - 0 - 1)) * x $$ (m - h - 1, 0)) =
       e0*y0 + e1*y1 + e2*y2 + e3*y3 +
       (∑h = 4..<m. of_int (N $$ (m - h - 1, m - 0 - 1)) * x $$ (m - h - 1, 0))"
      using linear_comb_of_y_part_2[
        OF four_sq m_v m_gt3 i0_in
           x0_def x1_def x2_def x3_def
           x0_eq x1_eq x2_eq x3_eq]
      by blast

    have simp_col: "m - 0 - 1 = m - 1"
      using m_gt3 by simp

    show ?thesis
      using e simp_col that by simp
  qed

  show ?thesis
    using coeff by blast
qed

lemma brc_L0123_from_last_four:
  fixes a b c d m :: nat
  fixes x :: "rat mat"
  fixes y0 y1 y2 y3 :: rat
  fixes x0 x1 x2 x3 :: rat
  assumes four_sq: "a^2 + b^2 + c^2 + d^2 = 𝗄 - Λ"
  assumes m_v: "𝗏 ≥ m"
  assumes m_gt3: "m > 3"
  assumes x0_def: "x0 = x $$ (m - 4, 0)"
  assumes x1_def: "x1 = x $$ (m - 3, 0)"
  assumes x2_def: "x2 = x $$ (m - 2, 0)"
  assumes x3_def: "x3 = x $$ (m - 1, 0)"
  assumes x0_eq: "x0 = one_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x1_eq: "x1 = two_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x2_eq: "x2 = three_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x3_eq: "x3 = four_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  shows
   "∃c00 c10 c20 c30 c01 c11 c21 c31 c02 c12 c22 c32 c03 c13 c23 c33.
      (∑h = 0..<m. of_int (N $$ (m - h - 1, m - 4)) * x $$ (m - h - 1, 0)) =
        c00*y0 + c10*y1 + c20*y2 + c30*y3 +
        (∑h = 4..<m. of_int (N $$ (m - h - 1, m - 4)) * x $$ (m - h - 1, 0))
    ∧ (∑h = 0..<m. of_int (N $$ (m - h - 1, m - 3)) * x $$ (m - h - 1, 0)) =
        c01*y0 + c11*y1 + c21*y2 + c31*y3 +
        (∑h = 4..<m. of_int (N $$ (m - h - 1, m - 3)) * x $$ (m - h - 1, 0))
    ∧ (∑h = 0..<m. of_int (N $$ (m - h - 1, m - 2)) * x $$ (m - h - 1, 0)) =
        c02*y0 + c12*y1 + c22*y2 + c32*y3 +
        (∑h = 4..<m. of_int (N $$ (m - h - 1, m - 2)) * x $$ (m - h - 1, 0))
    ∧ (∑h = 0..<m. of_int (N $$ (m - h - 1, m - 1)) * x $$ (m - h - 1, 0)) =
        c03*y0 + c13*y1 + c23*y2 + c33*y3 +
        (∑h = 4..<m. of_int (N $$ (m - h - 1, m - 1)) * x $$ (m - h - 1, 0))"
proof -
  obtain c00 c10 c20 c30 where L0:
    "(∑h = 0..<m. of_int (N $$ (m - h - 1, m - 4)) * x $$ (m - h - 1, 0)) =
      c00*y0 + c10*y1 + c20*y2 + c30*y3 +
      (∑h = 4..<m. of_int (N $$ (m - h - 1, m - 4)) * x $$ (m - h - 1, 0))"
    using brc_L0_from_last_four[
      OF four_sq m_v m_gt3 x0_def x1_def x2_def x3_def
         x0_eq x1_eq x2_eq x3_eq]
    by blast

  obtain c01 c11 c21 c31 where L1:
    "(∑h = 0..<m. of_int (N $$ (m - h - 1, m - 3)) * x $$ (m - h - 1, 0)) =
      c01*y0 + c11*y1 + c21*y2 + c31*y3 +
      (∑h = 4..<m. of_int (N $$ (m - h - 1, m - 3)) * x $$ (m - h - 1, 0))"
    using brc_L1_from_last_four[
      OF four_sq m_v m_gt3 x0_def x1_def x2_def x3_def
         x0_eq x1_eq x2_eq x3_eq]
    by blast

  obtain c02 c12 c22 c32 where L2:
    "(∑h = 0..<m. of_int (N $$ (m - h - 1, m - 2)) * x $$ (m - h - 1, 0)) =
      c02*y0 + c12*y1 + c22*y2 + c32*y3 +
      (∑h = 4..<m. of_int (N $$ (m - h - 1, m - 2)) * x $$ (m - h - 1, 0))"
    using brc_L2_from_last_four[
      OF four_sq m_v m_gt3 x0_def x1_def x2_def x3_def
         x0_eq x1_eq x2_eq x3_eq]
    by blast

  obtain c03 c13 c23 c33 where L3:
    "(∑h = 0..<m. of_int (N $$ (m - h - 1, m - 1)) * x $$ (m - h - 1, 0)) =
      c03*y0 + c13*y1 + c23*y2 + c33*y3 +
      (∑h = 4..<m. of_int (N $$ (m - h - 1, m - 1)) * x $$ (m - h - 1, 0))"
    using brc_L3_from_last_four[
      OF four_sq m_v m_gt3 x0_def x1_def x2_def x3_def
         x0_eq x1_eq x2_eq x3_eq]
    by blast

  show ?thesis
    using L0 L1 L2 L3 by blast
qed

lemma brc_last_four_square_if_choices:
  fixes a b c d m :: nat
  fixes x :: "rat mat"
  fixes y0 y1 y2 y3 :: rat
  fixes x0 x1 x2 x3 :: rat
  assumes four_sq: "a^2 + b^2 + c^2 + d^2 = 𝗄 - Λ"
  assumes m_v: "𝗏 ≥ m"
  assumes m_gt3: "m > 3"
  assumes x0_def: "x0 = x $$ (m - 4, 0)"
  assumes x1_def: "x1 = x $$ (m - 3, 0)"
  assumes x2_def: "x2 = x $$ (m - 2, 0)"
  assumes x3_def: "x3 = x $$ (m - 1, 0)"
  assumes x0_eq: "x0 = one_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x1_eq: "x1 = two_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x2_eq: "x2 = three_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x3_eq: "x3 = four_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes choices:
    "⋀e00 e10 e20 e30 e01 e11 e21 e31 e02 e12 e22 e32 e03 e13 e23 e33.
      ⟦
      (∑h = 0..<m. of_int (N $$ (m - h - 1, m - 4)) * x $$ (m - h - 1, 0)) =
        e00*y0 + e10*y1 + e20*y2 + e30*y3 +
        (∑h = 4..<m. of_int (N $$ (m - h - 1, m - 4)) * x $$ (m - h - 1, 0));
      (∑h = 0..<m. of_int (N $$ (m - h - 1, m - 3)) * x $$ (m - h - 1, 0)) =
        e01*y0 + e11*y1 + e21*y2 + e31*y3 +
        (∑h = 4..<m. of_int (N $$ (m - h - 1, m - 3)) * x $$ (m - h - 1, 0));
      (∑h = 0..<m. of_int (N $$ (m - h - 1, m - 2)) * x $$ (m - h - 1, 0)) =
        e02*y0 + e12*y1 + e22*y2 + e32*y3 +
        (∑h = 4..<m. of_int (N $$ (m - h - 1, m - 2)) * x $$ (m - h - 1, 0));
      (∑h = 0..<m. of_int (N $$ (m - h - 1, m - 1)) * x $$ (m - h - 1, 0)) =
        e03*y0 + e13*y1 + e23*y2 + e33*y3 +
        (∑h = 4..<m. of_int (N $$ (m - h - 1, m - 1)) * x $$ (m - h - 1, 0))
      ⟧ ⟹
      y0 =
        (if e00 = 1 then
          - (e10*y1 + e20*y2 + e30*y3 +
             (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
             (∑h∈{m..<𝗏}. of_int (N $$ (h,m-4)) * x $$ (h,0))) / 2
         else
          (e10*y1 + e20*y2 + e30*y3 +
           (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
           (∑h∈{m..<𝗏}. of_int (N $$ (h,m-4)) * x $$ (h,0))) / (1 - e00))
      ∧ y1 =
        (if e11 = 1 then
          - (e01*y0 + e21*y2 + e31*y3 +
             (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
             (∑h∈{m..<𝗏}. of_int (N $$ (h,m-3)) * x $$ (h,0))) / 2
         else
          (e01*y0 + e21*y2 + e31*y3 +
           (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
           (∑h∈{m..<𝗏}. of_int (N $$ (h,m-3)) * x $$ (h,0))) / (1 - e11))
      ∧ y2 =
        (if e22 = 1 then
          - (e02*y0 + e12*y1 + e32*y3 +
             (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
             (∑h∈{m..<𝗏}. of_int (N $$ (h,m-2)) * x $$ (h,0))) / 2
         else
          (e02*y0 + e12*y1 + e32*y3 +
           (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
           (∑h∈{m..<𝗏}. of_int (N $$ (h,m-2)) * x $$ (h,0))) / (1 - e22))
      ∧ y3 =
        (if e33 = 1 then
          - (e03*y0 + e13*y1 + e23*y2 +
             (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
             (∑h∈{m..<𝗏}. of_int (N $$ (h,m-1)) * x $$ (h,0))) / 2
         else
          (e03*y0 + e13*y1 + e23*y2 +
           (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
           (∑h∈{m..<𝗏}. of_int (N $$ (h,m-1)) * x $$ (h,0))) / (1 - e33))"
  shows
    "y0^2 =
      ((∑h∈{0..<m}. of_int (N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
      (∑h∈{m..<𝗏}. of_int (N $$ (h,m-4)) * x $$ (h,0)))^2
    ∧ y1^2 =
      ((∑h∈{0..<m}. of_int (N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
      (∑h∈{m..<𝗏}. of_int (N $$ (h,m-3)) * x $$ (h,0)))^2
    ∧ y2^2 =
      ((∑h∈{0..<m}. of_int (N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
      (∑h∈{m..<𝗏}. of_int (N $$ (h,m-2)) * x $$ (h,0)))^2
    ∧ y3^2 =
      ((∑h∈{0..<m}. of_int (N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
      (∑h∈{m..<𝗏}. of_int (N $$ (h,m-1)) * x $$ (h,0)))^2"
proof -
  obtain e00 e10 e20 e30 e01 e11 e21 e31 e02 e12 e22 e32 e03 e13 e23 e33
    where Ls:
      "(∑h = 0..<m. of_int (N $$ (m - h - 1, m - 4)) * x $$ (m - h - 1, 0)) =
        e00*y0 + e10*y1 + e20*y2 + e30*y3 +
        (∑h = 4..<m. of_int (N $$ (m - h - 1, m - 4)) * x $$ (m - h - 1, 0))"
      "(∑h = 0..<m. of_int (N $$ (m - h - 1, m - 3)) * x $$ (m - h - 1, 0)) =
        e01*y0 + e11*y1 + e21*y2 + e31*y3 +
        (∑h = 4..<m. of_int (N $$ (m - h - 1, m - 3)) * x $$ (m - h - 1, 0))"
      "(∑h = 0..<m. of_int (N $$ (m - h - 1, m - 2)) * x $$ (m - h - 1, 0)) =
        e02*y0 + e12*y1 + e22*y2 + e32*y3 +
        (∑h = 4..<m. of_int (N $$ (m - h - 1, m - 2)) * x $$ (m - h - 1, 0))"
      "(∑h = 0..<m. of_int (N $$ (m - h - 1, m - 1)) * x $$ (m - h - 1, 0)) =
        e03*y0 + e13*y1 + e23*y2 + e33*y3 +
        (∑h = 4..<m. of_int (N $$ (m - h - 1, m - 1)) * x $$ (m - h - 1, 0))"
    using brc_L0123_from_last_four[
      OF four_sq m_v m_gt3
         x0_def x1_def x2_def x3_def
         x0_eq x1_eq x2_eq x3_eq]
    by blast

  have ch_all:
    "y0 =
      (if e00 = 1 then
        - (e10*y1 + e20*y2 + e30*y3 +
           (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
           (∑h∈{m..<𝗏}. of_int (N $$ (h,m-4)) * x $$ (h,0))) / 2
       else
        (e10*y1 + e20*y2 + e30*y3 +
         (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
         (∑h∈{m..<𝗏}. of_int (N $$ (h,m-4)) * x $$ (h,0))) / (1 - e00))
    ∧ y1 =
      (if e11 = 1 then
        - (e01*y0 + e21*y2 + e31*y3 +
           (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
           (∑h∈{m..<𝗏}. of_int (N $$ (h,m-3)) * x $$ (h,0))) / 2
       else
        (e01*y0 + e21*y2 + e31*y3 +
         (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
         (∑h∈{m..<𝗏}. of_int (N $$ (h,m-3)) * x $$ (h,0))) / (1 - e11))
    ∧ y2 =
      (if e22 = 1 then
        - (e02*y0 + e12*y1 + e32*y3 +
           (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
           (∑h∈{m..<𝗏}. of_int (N $$ (h,m-2)) * x $$ (h,0))) / 2
       else
        (e02*y0 + e12*y1 + e32*y3 +
         (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
         (∑h∈{m..<𝗏}. of_int (N $$ (h,m-2)) * x $$ (h,0))) / (1 - e22))
    ∧ y3 =
      (if e33 = 1 then
        - (e03*y0 + e13*y1 + e23*y2 +
           (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
           (∑h∈{m..<𝗏}. of_int (N $$ (h,m-1)) * x $$ (h,0))) / 2
       else
        (e03*y0 + e13*y1 + e23*y2 +
         (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
         (∑h∈{m..<𝗏}. of_int (N $$ (h,m-1)) * x $$ (h,0))) / (1 - e33))"
    using choices[OF Ls] .

  have ch0: "y0 =
      (if e00 = 1 then
        - (e10*y1 + e20*y2 + e30*y3 +
           (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
           (∑h∈{m..<𝗏}. of_int (N $$ (h,m-4)) * x $$ (h,0))) / 2
       else
        (e10*y1 + e20*y2 + e30*y3 +
         (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
         (∑h∈{m..<𝗏}. of_int (N $$ (h,m-4)) * x $$ (h,0))) / (1 - e00))"
    using ch_all by blast

  have ch1: "y1 =
      (if e11 = 1 then
        - (e01*y0 + e21*y2 + e31*y3 +
           (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
           (∑h∈{m..<𝗏}. of_int (N $$ (h,m-3)) * x $$ (h,0))) / 2
       else
        (e01*y0 + e21*y2 + e31*y3 +
         (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
         (∑h∈{m..<𝗏}. of_int (N $$ (h,m-3)) * x $$ (h,0))) / (1 - e11))"
    using ch_all by blast

  have ch2: "y2 =
      (if e22 = 1 then
        - (e02*y0 + e12*y1 + e32*y3 +
           (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
           (∑h∈{m..<𝗏}. of_int (N $$ (h,m-2)) * x $$ (h,0))) / 2
       else
        (e02*y0 + e12*y1 + e32*y3 +
         (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
         (∑h∈{m..<𝗏}. of_int (N $$ (h,m-2)) * x $$ (h,0))) / (1 - e22))"
    using ch_all by blast

  have ch3: "y3 =
      (if e33 = 1 then
        - (e03*y0 + e13*y1 + e23*y2 +
           (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
           (∑h∈{m..<𝗏}. of_int (N $$ (h,m-1)) * x $$ (h,0))) / 2
       else
        (e03*y0 + e13*y1 + e23*y2 +
         (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
         (∑h∈{m..<𝗏}. of_int (N $$ (h,m-1)) * x $$ (h,0))) / (1 - e33))"
    using ch_all by blast

  show ?thesis
    using induction_step_0123_explicit[
      OF Ls(1) Ls(2) Ls(3) Ls(4) ch0 ch1 ch2 ch3]
    .
qed

definition brc_choice0 where
  "brc_choice0 e00 e10 e20 e30 y1 y2 y3 x m =
    (if e00 = 1 then
      - (e10*y1 + e20*y2 + e30*y3 +
         (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
         (∑h∈{m..<𝗏}. of_int (N $$ (h,m-4)) * x $$ (h,0))) / 2
     else
      (e10*y1 + e20*y2 + e30*y3 +
       (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
       (∑h∈{m..<𝗏}. of_int (N $$ (h,m-4)) * x $$ (h,0))) / (1 - e00))"

definition brc_choice1 where
  "brc_choice1 e01 e11 e21 e31 y0 y2 y3 x m =
    (if e11 = 1 then
      - (e01*y0 + e21*y2 + e31*y3 +
         (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
         (∑h∈{m..<𝗏}. of_int (N $$ (h,m-3)) * x $$ (h,0))) / 2
     else
      (e01*y0 + e21*y2 + e31*y3 +
       (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
       (∑h∈{m..<𝗏}. of_int (N $$ (h,m-3)) * x $$ (h,0))) / (1 - e11))"

definition brc_choice2 where
  "brc_choice2 e02 e12 e22 e32 y0 y1 y3 x m =
    (if e22 = 1 then
      - (e02*y0 + e12*y1 + e32*y3 +
         (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
         (∑h∈{m..<𝗏}. of_int (N $$ (h,m-2)) * x $$ (h,0))) / 2
     else
      (e02*y0 + e12*y1 + e32*y3 +
       (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
       (∑h∈{m..<𝗏}. of_int (N $$ (h,m-2)) * x $$ (h,0))) / (1 - e22))"

definition brc_choice3 where
  "brc_choice3 e03 e13 e23 e33 y0 y1 y2 x m =
    (if e33 = 1 then
      - (e03*y0 + e13*y1 + e23*y2 +
         (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
         (∑h∈{m..<𝗏}. of_int (N $$ (h,m-1)) * x $$ (h,0))) / 2
     else
      (e03*y0 + e13*y1 + e23*y2 +
       (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
       (∑h∈{m..<𝗏}. of_int (N $$ (h,m-1)) * x $$ (h,0))) / (1 - e33))"

lemma induction_step_0123_choices:
  fixes e00 e10 e20 e30 e01 e11 e21 e31 e02 e12 e22 e32 e03 e13 e23 e33 :: rat
  fixes y0 y1 y2 y3 :: rat
  fixes x :: "rat mat"
  fixes m :: nat
  assumes L0:
    "(∑h∈{0..<m}. of_int (N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) =
      e00*y0 + e10*y1 + e20*y2 + e30*y3 +
      (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-4)) * x $$ (m-h-1,0))"
  assumes L1:
    "(∑h∈{0..<m}. of_int (N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) =
      e01*y0 + e11*y1 + e21*y2 + e31*y3 +
      (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-3)) * x $$ (m-h-1,0))"
  assumes L2:
    "(∑h∈{0..<m}. of_int (N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) =
      e02*y0 + e12*y1 + e22*y2 + e32*y3 +
      (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-2)) * x $$ (m-h-1,0))"
  assumes L3:
    "(∑h∈{0..<m}. of_int (N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) =
      e03*y0 + e13*y1 + e23*y2 + e33*y3 +
      (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-1)) * x $$ (m-h-1,0))"
  assumes ch0: "y0 = brc_choice0 e00 e10 e20 e30 y1 y2 y3 x m"
  assumes ch1: "y1 = brc_choice1 e01 e11 e21 e31 y0 y2 y3 x m"
  assumes ch2: "y2 = brc_choice2 e02 e12 e22 e32 y0 y1 y3 x m"
  assumes ch3: "y3 = brc_choice3 e03 e13 e23 e33 y0 y1 y2 x m"
  shows
    "y0^2 =
      ((∑h∈{0..<m}. of_int (N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
       (∑h∈{m..<𝗏}. of_int (N $$ (h,m-4)) * x $$ (h,0)))^2
    ∧ y1^2 =
      ((∑h∈{0..<m}. of_int (N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
       (∑h∈{m..<𝗏}. of_int (N $$ (h,m-3)) * x $$ (h,0)))^2
    ∧ y2^2 =
      ((∑h∈{0..<m}. of_int (N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
       (∑h∈{m..<𝗏}. of_int (N $$ (h,m-2)) * x $$ (h,0)))^2
    ∧ y3^2 =
      ((∑h∈{0..<m}. of_int (N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
       (∑h∈{m..<𝗏}. of_int (N $$ (h,m-1)) * x $$ (h,0)))^2"
  using induction_step_0123_explicit[
    OF L0 L1 L2 L3]
  using ch0 ch1 ch2 ch3
  unfolding brc_choice0_def brc_choice1_def brc_choice2_def brc_choice3_def
  by blast

lemma brc_last_four_square_if_choices_short:
  fixes a b c d m :: nat
  fixes x :: "rat mat"
  fixes y0 y1 y2 y3 :: rat
  fixes x0 x1 x2 x3 :: rat
  assumes four_sq: "a^2 + b^2 + c^2 + d^2 = 𝗄 - Λ"
  assumes m_v: "𝗏 ≥ m"
  assumes m_gt3: "m > 3"
  assumes x0_def: "x0 = x $$ (m - 4, 0)"
  assumes x1_def: "x1 = x $$ (m - 3, 0)"
  assumes x2_def: "x2 = x $$ (m - 2, 0)"
  assumes x3_def: "x3 = x $$ (m - 1, 0)"
  assumes x0_eq: "x0 = one_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x1_eq: "x1 = two_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x2_eq: "x2 = three_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x3_eq: "x3 = four_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes choices:
    "⋀e00 e10 e20 e30 e01 e11 e21 e31 e02 e12 e22 e32 e03 e13 e23 e33.
      ⟦
      (∑h = 0..<m. of_int (N $$ (m - h - 1, m - 4)) * x $$ (m - h - 1, 0)) =
        e00*y0 + e10*y1 + e20*y2 + e30*y3 +
        (∑h = 4..<m. of_int (N $$ (m - h - 1, m - 4)) * x $$ (m - h - 1, 0));
      (∑h = 0..<m. of_int (N $$ (m - h - 1, m - 3)) * x $$ (m - h - 1, 0)) =
        e01*y0 + e11*y1 + e21*y2 + e31*y3 +
        (∑h = 4..<m. of_int (N $$ (m - h - 1, m - 3)) * x $$ (m - h - 1, 0));
      (∑h = 0..<m. of_int (N $$ (m - h - 1, m - 2)) * x $$ (m - h - 1, 0)) =
        e02*y0 + e12*y1 + e22*y2 + e32*y3 +
        (∑h = 4..<m. of_int (N $$ (m - h - 1, m - 2)) * x $$ (m - h - 1, 0));
      (∑h = 0..<m. of_int (N $$ (m - h - 1, m - 1)) * x $$ (m - h - 1, 0)) =
        e03*y0 + e13*y1 + e23*y2 + e33*y3 +
        (∑h = 4..<m. of_int (N $$ (m - h - 1, m - 1)) * x $$ (m - h - 1, 0))
      ⟧ ⟹
      y0 = brc_choice0 e00 e10 e20 e30 y1 y2 y3 x m
    ∧ y1 = brc_choice1 e01 e11 e21 e31 y0 y2 y3 x m
    ∧ y2 = brc_choice2 e02 e12 e22 e32 y0 y1 y3 x m
    ∧ y3 = brc_choice3 e03 e13 e23 e33 y0 y1 y2 x m"
  shows
    "y0^2 =
      ((∑h∈{0..<m}. of_int (N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
       (∑h∈{m..<𝗏}. of_int (N $$ (h,m-4)) * x $$ (h,0)))^2
    ∧ y1^2 =
      ((∑h∈{0..<m}. of_int (N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
       (∑h∈{m..<𝗏}. of_int (N $$ (h,m-3)) * x $$ (h,0)))^2
    ∧ y2^2 =
      ((∑h∈{0..<m}. of_int (N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
       (∑h∈{m..<𝗏}. of_int (N $$ (h,m-2)) * x $$ (h,0)))^2
    ∧ y3^2 =
      ((∑h∈{0..<m}. of_int (N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
       (∑h∈{m..<𝗏}. of_int (N $$ (h,m-1)) * x $$ (h,0)))^2"
proof -
  obtain e00 e10 e20 e30 e01 e11 e21 e31 e02 e12 e22 e32 e03 e13 e23 e33
    where Ls:
      "(∑h = 0..<m. of_int (N $$ (m - h - 1, m - 4)) * x $$ (m - h - 1, 0)) =
        e00*y0 + e10*y1 + e20*y2 + e30*y3 +
        (∑h = 4..<m. of_int (N $$ (m - h - 1, m - 4)) * x $$ (m - h - 1, 0))"
      "(∑h = 0..<m. of_int (N $$ (m - h - 1, m - 3)) * x $$ (m - h - 1, 0)) =
        e01*y0 + e11*y1 + e21*y2 + e31*y3 +
        (∑h = 4..<m. of_int (N $$ (m - h - 1, m - 3)) * x $$ (m - h - 1, 0))"
      "(∑h = 0..<m. of_int (N $$ (m - h - 1, m - 2)) * x $$ (m - h - 1, 0)) =
        e02*y0 + e12*y1 + e22*y2 + e32*y3 +
        (∑h = 4..<m. of_int (N $$ (m - h - 1, m - 2)) * x $$ (m - h - 1, 0))"
      "(∑h = 0..<m. of_int (N $$ (m - h - 1, m - 1)) * x $$ (m - h - 1, 0)) =
        e03*y0 + e13*y1 + e23*y2 + e33*y3 +
        (∑h = 4..<m. of_int (N $$ (m - h - 1, m - 1)) * x $$ (m - h - 1, 0))"
    using brc_L0123_from_last_four[
      OF four_sq m_v m_gt3
         x0_def x1_def x2_def x3_def
         x0_eq x1_eq x2_eq x3_eq]
    by blast

  have ch_all:
    "y0 = brc_choice0 e00 e10 e20 e30 y1 y2 y3 x m
   ∧ y1 = brc_choice1 e01 e11 e21 e31 y0 y2 y3 x m
   ∧ y2 = brc_choice2 e02 e12 e22 e32 y0 y1 y3 x m
   ∧ y3 = brc_choice3 e03 e13 e23 e33 y0 y1 y2 x m"
    using choices[OF Ls] .

  show ?thesis
    using induction_step_0123_choices[
      OF Ls(1) Ls(2) Ls(3) Ls(4)]
    using ch_all
    by blast
qed

lemma brc_choice0_exists:
  fixes e00 e10 e20 e30 y1 y2 y3 :: rat
  fixes x :: "rat mat"
  fixes m :: nat
  shows "∃y0. y0 = brc_choice0 e00 e10 e20 e30 y1 y2 y3 x m"
  by blast

lemma brc_choice1_exists:
  fixes e01 e11 e21 e31 y0 y2 y3 :: rat
  fixes x :: "rat mat"
  fixes m :: nat
  shows "∃y1. y1 = brc_choice1 e01 e11 e21 e31 y0 y2 y3 x m"
  by blast

lemma brc_choice2_exists:
  fixes e02 e12 e22 e32 y0 y1 y3 :: rat
  fixes x :: "rat mat"
  fixes m :: nat
  shows "∃y2. y2 = brc_choice2 e02 e12 e22 e32 y0 y1 y3 x m"
  by blast

lemma brc_choice3_exists:
  fixes e03 e13 e23 e33 y0 y1 y2 :: rat
  fixes x :: "rat mat"
  fixes m :: nat
  shows "∃y3. y3 = brc_choice3 e03 e13 e23 e33 y0 y1 y2 x m"
  by blast

lemma brc_choice0_square:
  fixes e00 e10 e20 e30 y1 y2 y3 :: rat
  fixes x :: "rat mat"
  fixes m :: nat
  defines "y0 ≡ brc_choice0 e00 e10 e20 e30 y1 y2 y3 x m"
  assumes L0:
    "(∑h∈{0..<m}. of_int (N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) =
      e00*y0 + e10*y1 + e20*y2 + e30*y3 +
      (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-4)) * x $$ (m-h-1,0))"
  shows
    "y0^2 =
      ((∑h∈{0..<m}. of_int (N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
       (∑h∈{m..<𝗏}. of_int (N $$ (h,m-4)) * x $$ (h,0)))^2"
  using induction_step_0_explicit[OF L0]
  unfolding y0_def brc_choice0_def
  by simp

lemma brc_choice1_square:
  fixes e01 e11 e21 e31 y0 y2 y3 :: rat
  fixes x :: "rat mat"
  fixes m :: nat
  defines "y1 ≡ brc_choice1 e01 e11 e21 e31 y0 y2 y3 x m"
  assumes L1:
    "(∑h∈{0..<m}. of_int (N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) =
      e01*y0 + e11*y1 + e21*y2 + e31*y3 +
      (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-3)) * x $$ (m-h-1,0))"
  shows
    "y1^2 =
      ((∑h∈{0..<m}. of_int (N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
       (∑h∈{m..<𝗏}. of_int (N $$ (h,m-3)) * x $$ (h,0)))^2"
  using induction_step_1_explicit[OF L1]
  unfolding y1_def brc_choice1_def
  by simp

lemma brc_choice2_square:
  fixes e02 e12 e22 e32 y0 y1 y3 :: rat
  fixes x :: "rat mat"
  fixes m :: nat
  defines "y2 ≡ brc_choice2 e02 e12 e22 e32 y0 y1 y3 x m"
  assumes L2:
    "(∑h∈{0..<m}. of_int (N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) =
      e02*y0 + e12*y1 + e22*y2 + e32*y3 +
      (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-2)) * x $$ (m-h-1,0))"
  shows
    "y2^2 =
      ((∑h∈{0..<m}. of_int (N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
       (∑h∈{m..<𝗏}. of_int (N $$ (h,m-2)) * x $$ (h,0)))^2"
  using induction_step_2_explicit[OF L2]
  unfolding y2_def brc_choice2_def
  by simp

lemma brc_choice3_square:
  fixes e03 e13 e23 e33 y0 y1 y2 :: rat
  fixes x :: "rat mat"
  fixes m :: nat
  defines "y3 ≡ brc_choice3 e03 e13 e23 e33 y0 y1 y2 x m"
  assumes L3:
    "(∑h∈{0..<m}. of_int (N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) =
      e03*y0 + e13*y1 + e23*y2 + e33*y3 +
      (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-1)) * x $$ (m-h-1,0))"
  shows
    "y3^2 =
      ((∑h∈{0..<m}. of_int (N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
       (∑h∈{m..<𝗏}. of_int (N $$ (h,m-1)) * x $$ (h,0)))^2"
  using induction_step_3_explicit[OF L3]
  unfolding y3_def brc_choice3_def
  by simp

lemma brc_choice0123_square:
  fixes e00 e10 e20 e30 e01 e11 e21 e31 e02 e12 e22 e32 e03 e13 e23 e33 :: rat
  fixes y0 y1 y2 y3 :: rat
  fixes x :: "rat mat"
  fixes m :: nat
  assumes y0_def: "y0 = brc_choice0 e00 e10 e20 e30 y1 y2 y3 x m"
  assumes y1_def: "y1 = brc_choice1 e01 e11 e21 e31 y0 y2 y3 x m"
  assumes y2_def: "y2 = brc_choice2 e02 e12 e22 e32 y0 y1 y3 x m"
  assumes y3_def: "y3 = brc_choice3 e03 e13 e23 e33 y0 y1 y2 x m"
  assumes L0:
    "(∑h∈{0..<m}. of_int (N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) =
      e00*y0 + e10*y1 + e20*y2 + e30*y3 +
      (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-4)) * x $$ (m-h-1,0))"
  assumes L1:
    "(∑h∈{0..<m}. of_int (N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) =
      e01*y0 + e11*y1 + e21*y2 + e31*y3 +
      (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-3)) * x $$ (m-h-1,0))"
  assumes L2:
    "(∑h∈{0..<m}. of_int (N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) =
      e02*y0 + e12*y1 + e22*y2 + e32*y3 +
      (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-2)) * x $$ (m-h-1,0))"
  assumes L3:
    "(∑h∈{0..<m}. of_int (N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) =
      e03*y0 + e13*y1 + e23*y2 + e33*y3 +
      (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-1)) * x $$ (m-h-1,0))"
  shows
    "y0^2 =
      ((∑h∈{0..<m}. of_int (N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
       (∑h∈{m..<𝗏}. of_int (N $$ (h,m-4)) * x $$ (h,0)))^2
    ∧ y1^2 =
      ((∑h∈{0..<m}. of_int (N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
       (∑h∈{m..<𝗏}. of_int (N $$ (h,m-3)) * x $$ (h,0)))^2
    ∧ y2^2 =
      ((∑h∈{0..<m}. of_int (N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
       (∑h∈{m..<𝗏}. of_int (N $$ (h,m-2)) * x $$ (h,0)))^2
    ∧ y3^2 =
      ((∑h∈{0..<m}. of_int (N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
       (∑h∈{m..<𝗏}. of_int (N $$ (h,m-1)) * x $$ (h,0)))^2"
  using induction_step_0123_choices[
    OF L0 L1 L2 L3 y0_def y1_def y2_def y3_def]
  . 

lemma brc_last_four_square_from_choices:
  fixes a b c d m :: nat
  fixes x :: "rat mat"
  fixes y0 y1 y2 y3 :: rat
  fixes x0 x1 x2 x3 :: rat
  assumes four_sq: "a^2 + b^2 + c^2 + d^2 = 𝗄 - Λ"
  assumes m_v: "𝗏 ≥ m"
  assumes m_gt3: "m > 3"
  assumes x0_def: "x0 = x $$ (m - 4, 0)"
  assumes x1_def: "x1 = x $$ (m - 3, 0)"
  assumes x2_def: "x2 = x $$ (m - 2, 0)"
  assumes x3_def: "x3 = x $$ (m - 1, 0)"
  assumes x0_eq: "x0 = one_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x1_eq: "x1 = two_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x2_eq: "x2 = three_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x3_eq: "x3 = four_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes choices:
    "⋀e00 e10 e20 e30 e01 e11 e21 e31 e02 e12 e22 e32 e03 e13 e23 e33.
      ⟦
      (∑h = 0..<m. of_int (N $$ (m - h - 1, m - 4)) * x $$ (m - h - 1, 0)) =
        e00*y0 + e10*y1 + e20*y2 + e30*y3 +
        (∑h = 4..<m. of_int (N $$ (m - h - 1, m - 4)) * x $$ (m - h - 1, 0));
      (∑h = 0..<m. of_int (N $$ (m - h - 1, m - 3)) * x $$ (m - h - 1, 0)) =
        e01*y0 + e11*y1 + e21*y2 + e31*y3 +
        (∑h = 4..<m. of_int (N $$ (m - h - 1, m - 3)) * x $$ (m - h - 1, 0));
      (∑h = 0..<m. of_int (N $$ (m - h - 1, m - 2)) * x $$ (m - h - 1, 0)) =
        e02*y0 + e12*y1 + e22*y2 + e32*y3 +
        (∑h = 4..<m. of_int (N $$ (m - h - 1, m - 2)) * x $$ (m - h - 1, 0));
      (∑h = 0..<m. of_int (N $$ (m - h - 1, m - 1)) * x $$ (m - h - 1, 0)) =
        e03*y0 + e13*y1 + e23*y2 + e33*y3 +
        (∑h = 4..<m. of_int (N $$ (m - h - 1, m - 1)) * x $$ (m - h - 1, 0))
      ⟧ ⟹
      y0 = brc_choice0 e00 e10 e20 e30 y1 y2 y3 x m
    ∧ y1 = brc_choice1 e01 e11 e21 e31 y0 y2 y3 x m
    ∧ y2 = brc_choice2 e02 e12 e22 e32 y0 y1 y3 x m
    ∧ y3 = brc_choice3 e03 e13 e23 e33 y0 y1 y2 x m"
  shows
    "y0^2 =
      ((∑h∈{0..<m}. of_int (N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
       (∑h∈{m..<𝗏}. of_int (N $$ (h,m-4)) * x $$ (h,0)))^2
    ∧ y1^2 =
      ((∑h∈{0..<m}. of_int (N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
       (∑h∈{m..<𝗏}. of_int (N $$ (h,m-3)) * x $$ (h,0)))^2
    ∧ y2^2 =
      ((∑h∈{0..<m}. of_int (N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
       (∑h∈{m..<𝗏}. of_int (N $$ (h,m-2)) * x $$ (h,0)))^2
    ∧ y3^2 =
      ((∑h∈{0..<m}. of_int (N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
       (∑h∈{m..<𝗏}. of_int (N $$ (h,m-1)) * x $$ (h,0)))^2"
  using brc_last_four_square_if_choices_short[
    OF four_sq m_v m_gt3
       x0_def x1_def x2_def x3_def
       x0_eq x1_eq x2_eq x3_eq choices]
  .

lemma brc_sequential_elimination_step:
  fixes e00 e10 e20 e30 e01 e11 e21 e31 e02 e12 e22 e32 e03 e13 e23 e33 :: rat
  fixes y1a y2a y3a :: rat
  fixes x :: "rat mat"
  fixes m :: nat
  defines "y0 ≡ brc_choice0 e00 e10 e20 e30 y1a y2a y3a x m"
  defines "y1 ≡ brc_choice1 e01 e11 e21 e31 y0 y2a y3a x m"
  defines "y2 ≡ brc_choice2 e02 e12 e22 e32 y0 y1 y3a x m"
  defines "y3 ≡ brc_choice3 e03 e13 e23 e33 y0 y1 y2 x m"
  assumes L0:
    "(∑h∈{0..<m}. of_int (N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) =
      e00*y0 + e10*y1a + e20*y2a + e30*y3a +
      (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-4)) * x $$ (m-h-1,0))"
  assumes L1:
    "(∑h∈{0..<m}. of_int (N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) =
      e01*y0 + e11*y1 + e21*y2a + e31*y3a +
      (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-3)) * x $$ (m-h-1,0))"
  assumes L2:
    "(∑h∈{0..<m}. of_int (N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) =
      e02*y0 + e12*y1 + e22*y2 + e32*y3a +
      (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-2)) * x $$ (m-h-1,0))"
  assumes L3:
    "(∑h∈{0..<m}. of_int (N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) =
      e03*y0 + e13*y1 + e23*y2 + e33*y3 +
      (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-1)) * x $$ (m-h-1,0))"
  shows
    "y0^2 =
      ((∑h∈{0..<m}. of_int (N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
       (∑h∈{m..<𝗏}. of_int (N $$ (h,m-4)) * x $$ (h,0)))^2
    ∧ y1^2 =
      ((∑h∈{0..<m}. of_int (N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
       (∑h∈{m..<𝗏}. of_int (N $$ (h,m-3)) * x $$ (h,0)))^2
    ∧ y2^2 =
      ((∑h∈{0..<m}. of_int (N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
       (∑h∈{m..<𝗏}. of_int (N $$ (h,m-2)) * x $$ (h,0)))^2
    ∧ y3^2 =
      ((∑h∈{0..<m}. of_int (N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
       (∑h∈{m..<𝗏}. of_int (N $$ (h,m-1)) * x $$ (h,0)))^2"
proof -
  have L0': "(∑h∈{0..<m}. of_int (N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) =
      e00*(brc_choice0 e00 e10 e20 e30 y1a y2a y3a x m)
      + e10*y1a + e20*y2a + e30*y3a +
      (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-4)) * x $$ (m-h-1,0))"
    using L0 unfolding y0_def by simp

  have S0:
    "y0^2 =
      ((∑h∈{0..<m}. of_int (N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
       (∑h∈{m..<𝗏}. of_int (N $$ (h,m-4)) * x $$ (h,0)))^2"
    using brc_choice0_square[OF L0']
    unfolding y0_def by simp

  have L1': "(∑h∈{0..<m}. of_int (N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) =
      e01*y0 + e11*(brc_choice1 e01 e11 e21 e31 y0 y2a y3a x m)
      + e21*y2a + e31*y3a +
      (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-3)) * x $$ (m-h-1,0))"
    using L1 unfolding y1_def by simp

  have S1:
    "y1^2 =
      ((∑h∈{0..<m}. of_int (N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
       (∑h∈{m..<𝗏}. of_int (N $$ (h,m-3)) * x $$ (h,0)))^2"
    using brc_choice1_square[OF L1']
    unfolding y1_def by simp

  have L2': "(∑h∈{0..<m}. of_int (N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) =
      e02*y0 + e12*y1
      + e22*(brc_choice2 e02 e12 e22 e32 y0 y1 y3a x m)
      + e32*y3a +
      (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-2)) * x $$ (m-h-1,0))"
    using L2 unfolding y2_def by simp

  have S2:
    "y2^2 =
      ((∑h∈{0..<m}. of_int (N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
       (∑h∈{m..<𝗏}. of_int (N $$ (h,m-2)) * x $$ (h,0)))^2"
    using brc_choice2_square[OF L2']
    unfolding y2_def by simp

  have L3': "(∑h∈{0..<m}. of_int (N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) =
      e03*y0 + e13*y1 + e23*y2
      + e33*(brc_choice3 e03 e13 e23 e33 y0 y1 y2 x m) +
      (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-1)) * x $$ (m-h-1,0))"
    using L3 unfolding y3_def by simp

  have S3:
    "y3^2 =
      ((∑h∈{0..<m}. of_int (N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
       (∑h∈{m..<𝗏}. of_int (N $$ (h,m-1)) * x $$ (h,0)))^2"
    using brc_choice3_square[OF L3']
    unfolding y3_def by simp

  show ?thesis
    using S0 S1 S2 S3 by blast
qed

lemma y_inv_norm_brc:
  fixes a b c d :: nat
  fixes y0 y1 y2 y3 :: rat
  assumes four_sq: "a^2 + b^2 + c^2 + d^2 = 𝗄 - Λ"
  shows
    "let xs = y_inv_of ((a,b,c,d),(y0,y1,y2,y3)) in
      of_nat (𝗄 - Λ) *
        (one_of xs^2 + two_of xs^2 + three_of xs^2 + four_of xs^2)
      =
      y0^2 + y1^2 + y2^2 + y3^2"
proof -
  let ?xs = "y_inv_of ((a,b,c,d),(y0,y1,y2,y3))"

  have nz: "a^2 + b^2 + c^2 + d^2 ≠ 0"
    using four_sq blocksize_gt_index by simp

  have yback:
    "y_of ((a,b,c,d), ?xs) = (y0,y1,y2,y3)"
    using y_inverses_part_2[OF nz, of y0 y1 y2 y3]
    by simp

  have norm:
    "let y = y_of ((a,b,c,d), ?xs) in
      one_of y ^ 2 + two_of y ^ 2 + three_of y ^ 2 + four_of y ^ 2
      =
      of_nat (𝗄 - Λ) *
        (one_of ?xs^2 + two_of ?xs^2 + three_of ?xs^2 + four_of ?xs^2)"
    using y_of_norm_brc[OF four_sq,
      of "one_of ?xs" "two_of ?xs" "three_of ?xs" "four_of ?xs"]
    by (simp add: Let_def)

  show ?thesis
    using norm yback
    by (simp add: Let_def)
qed

lemma y_norm_replace_brc:
  fixes a b c d :: nat
  fixes y0 y1 y2 y3 x0 x1 x2 x3 :: rat
  assumes four_sq: "a^2 + b^2 + c^2 + d^2 = 𝗄 - Λ"
  assumes x0_eq: "x0 = one_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x1_eq: "x1 = two_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x2_eq: "x2 = three_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x3_eq: "x3 = four_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  shows
    "of_nat (𝗄 - Λ) * (x0^2 + x1^2 + x2^2 + x3^2)
     =
     y0^2 + y1^2 + y2^2 + y3^2"
proof -
  let ?xs = "y_inv_of ((a,b,c,d),(y0,y1,y2,y3))"

  have norm:
    "of_nat (𝗄 - Λ) *
      (one_of ?xs^2 + two_of ?xs^2 + three_of ?xs^2 + four_of ?xs^2)
     =
     y0^2 + y1^2 + y2^2 + y3^2"
    using y_inv_norm_brc[OF four_sq, of y0 y1 y2 y3]
    by (simp add: Let_def)

  show ?thesis
    using norm x0_eq x1_eq x2_eq x3_eq
    by simp
qed

lemma brc_four_var_identity_y:
  fixes a b c d m :: nat
  fixes y0 y1 y2 y3 :: rat
  assumes four_sq: "a^2 + b^2 + c^2 + d^2 = 𝗄 - Λ"
  assumes m_props: "m > 3" "𝗏 ≥ m"
  defines "xs ≡ y_inv_of ((a,b,c,d),(y0,y1,y2,y3))"
  shows
   "(∑i∈{0..<𝗏}. (∑h∈{0..<𝗏}. of_int (N $$ (h,i)) *
      (mat 𝗏 1 (λ(i,j).
        if j = 0 then
          (if i = m - 4 then one_of xs
           else if i = m - 3 then two_of xs
           else if i = m - 2 then three_of xs
           else if i = m - 1 then four_of xs
           else 0)
        else 0)) $$ (h,0))^2)
    =
    of_int (int Λ) *
      (one_of xs + two_of xs + three_of xs + four_of xs)^2
    + y0^2 + y1^2 + y2^2 + y3^2"
proof -
  have base:
   "(∑i∈{0..<𝗏}. (∑h∈{0..<𝗏}. of_int (N $$ (h,i)) *
      (mat 𝗏 1 (λ(i,j).
        if j = 0 then
          (if i = m - 4 then one_of xs
           else if i = m - 3 then two_of xs
           else if i = m - 2 then three_of xs
           else if i = m - 1 then four_of xs
           else 0)
        else 0)) $$ (h,0))^2)
    =
    of_int (int Λ) *
      (one_of xs + two_of xs + three_of xs + four_of xs)^2
    + of_int (int (𝗄 - Λ)) *
      (one_of xs^2 + two_of xs^2 + three_of xs^2 + four_of xs^2)"
    using brc_v_1_mod_4_identity[
      OF four_sq m_props,
      of "one_of xs" "two_of xs" "three_of xs" "four_of xs"]
    by simp

  have norm:
    "of_int (int (𝗄 - Λ)) *
      (one_of xs^2 + two_of xs^2 + three_of xs^2 + four_of xs^2)
     =
     y0^2 + y1^2 + y2^2 + y3^2"
    unfolding xs_def
    using y_inv_norm_brc[OF four_sq, of y0 y1 y2 y3]
    by (simp add: Let_def)

  show ?thesis
    using base norm by simp
qed

lemma brc_four_var_identity_y_named:
  fixes a b c d m :: nat
  fixes y0 y1 y2 y3 x0 x1 x2 x3 :: rat
  assumes four_sq: "a^2 + b^2 + c^2 + d^2 = 𝗄 - Λ"
  assumes m_props: "m > 3" "𝗏 ≥ m"
  assumes x0_eq: "x0 = one_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x1_eq: "x1 = two_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x2_eq: "x2 = three_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x3_eq: "x3 = four_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  shows
   "(∑i∈{0..<𝗏}. (∑h∈{0..<𝗏}. of_int (N $$ (h,i)) *
      (mat 𝗏 1 (λ(i,j).
        if j = 0 then
          (if i = m - 4 then x0
           else if i = m - 3 then x1
           else if i = m - 2 then x2
           else if i = m - 1 then x3
           else 0)
        else 0)) $$ (h,0))^2)
    =
    of_int (int Λ) * (x0 + x1 + x2 + x3)^2
    + y0^2 + y1^2 + y2^2 + y3^2"
proof -
  let ?xs = "y_inv_of ((a,b,c,d),(y0,y1,y2,y3))"

  have main:
   "(∑i∈{0..<𝗏}. (∑h∈{0..<𝗏}. of_int (N $$ (h,i)) *
      (mat 𝗏 1 (λ(i,j).
        if j = 0 then
          (if i = m - 4 then one_of ?xs
           else if i = m - 3 then two_of ?xs
           else if i = m - 2 then three_of ?xs
           else if i = m - 1 then four_of ?xs
           else 0)
        else 0)) $$ (h,0))^2)
    =
    of_int (int Λ) *
      (one_of ?xs + two_of ?xs + three_of ?xs + four_of ?xs)^2
    + y0^2 + y1^2 + y2^2 + y3^2"
    using brc_four_var_identity_y[OF four_sq m_props, of y0 y1 y2 y3]
    by simp

  have xs0: "one_of ?xs = x0"
    using x0_eq by simp
  have xs1: "two_of ?xs = x1"
    using x1_eq by simp
  have xs2: "three_of ?xs = x2"
    using x2_eq by simp
  have xs3: "four_of ?xs = x3"
    using x3_eq by simp

  have sum_eq:
    "one_of ?xs + two_of ?xs + three_of ?xs + four_of ?xs
     = x0 + x1 + x2 + x3"
    using x0_eq x1_eq x2_eq x3_eq
    by simp

  have inner_eq:
    "⋀h. (if h = m - 4 then one_of ?xs
          else if h = m - 3 then two_of ?xs
          else if h = m - 2 then three_of ?xs
          else if h = m - 1 then four_of ?xs
          else 0)
       =
         (if h = m - 4 then x0
          else if h = m - 3 then x1
          else if h = m - 2 then x2
          else if h = m - 1 then x3
          else 0)"
    using xs0 xs1 xs2 xs3
    by auto

  show ?thesis
    using main inner_eq sum_eq
    by simp
qed

lemma brc_four_var_identity_for_sparse_x:
  fixes a b c d m :: nat
  fixes y0 y1 y2 y3 x0 x1 x2 x3 :: rat
  fixes x :: "rat mat"
  assumes four_sq: "a^2 + b^2 + c^2 + d^2 = 𝗄 - Λ"
  assumes m_props: "m > 3" "𝗏 ≥ m"
  assumes x_def:
    "x = mat 𝗏 1 (λ(i,j).
        if j = 0 then
          (if i = m - 4 then x0
           else if i = m - 3 then x1
           else if i = m - 2 then x2
           else if i = m - 1 then x3
           else 0)
        else 0)"
  assumes x0_eq: "x0 = one_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x1_eq: "x1 = two_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x2_eq: "x2 = three_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x3_eq: "x3 = four_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  shows
   "(∑i∈{0..<𝗏}. (∑h∈{0..<𝗏}. of_int (N $$ (h,i)) * x $$ (h,0))^2)
    =
    of_int (int Λ) * (x0 + x1 + x2 + x3)^2
    + y0^2 + y1^2 + y2^2 + y3^2"
  unfolding x_def
  using brc_four_var_identity_y_named[
    OF four_sq m_props x0_eq x1_eq x2_eq x3_eq]
  by simp

lemma sparse_x_last_four_entries:
  fixes x :: "rat mat"
  fixes x0 x1 x2 x3 :: rat
  assumes m_props: "m > 3" "𝗏 ≥ m"
  assumes x_def:
    "x = mat 𝗏 1 (λ(i,j).
        if j = 0 then
          (if i = m - 4 then x0
           else if i = m - 3 then x1
           else if i = m - 2 then x2
           else if i = m - 1 then x3
           else 0)
        else 0)"
  shows
    "x $$ (m - 4,0) = x0"
    "x $$ (m - 3,0) = x1"
    "x $$ (m - 2,0) = x2"
    "x $$ (m - 1,0) = x3"
proof -
  have m4: "4 ≤ m"
    using m_props by simp

  show "x $$ (m - 4,0) = x0"
    unfolding x_def using m_props m4 by simp

  show "x $$ (m - 3,0) = x1"
    unfolding x_def using m_props m4 by auto

  show "x $$ (m - 2,0) = x2"
    unfolding x_def using m_props m4 by auto

  show "x $$ (m - 1,0) = x3"
    unfolding x_def using m_props m4 by auto
qed

lemma brc_sparse_x_L0123:
  fixes a b c d m :: nat
  fixes y0 y1 y2 y3 x0 x1 x2 x3 :: rat
  fixes x :: "rat mat"
  assumes four_sq: "a^2 + b^2 + c^2 + d^2 = 𝗄 - Λ"
  assumes m_props: "m > 3" "𝗏 ≥ m"
  assumes x_def:
    "x = mat 𝗏 1 (λ(i,j).
        if j = 0 then
          (if i = m - 4 then x0
           else if i = m - 3 then x1
           else if i = m - 2 then x2
           else if i = m - 1 then x3
           else 0)
        else 0)"
  assumes x0_eq: "x0 = one_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x1_eq: "x1 = two_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x2_eq: "x2 = three_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x3_eq: "x3 = four_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  shows
   "∃c00 c10 c20 c30 c01 c11 c21 c31 c02 c12 c22 c32 c03 c13 c23 c33.
      (∑h = 0..<m. of_int (N $$ (m - h - 1, m - 4)) * x $$ (m - h - 1, 0)) =
        c00*y0 + c10*y1 + c20*y2 + c30*y3 +
        (∑h = 4..<m. of_int (N $$ (m - h - 1, m - 4)) * x $$ (m - h - 1, 0))
    ∧ (∑h = 0..<m. of_int (N $$ (m - h - 1, m - 3)) * x $$ (m - h - 1, 0)) =
        c01*y0 + c11*y1 + c21*y2 + c31*y3 +
        (∑h = 4..<m. of_int (N $$ (m - h - 1, m - 3)) * x $$ (m - h - 1, 0))
    ∧ (∑h = 0..<m. of_int (N $$ (m - h - 1, m - 2)) * x $$ (m - h - 1, 0)) =
        c02*y0 + c12*y1 + c22*y2 + c32*y3 +
        (∑h = 4..<m. of_int (N $$ (m - h - 1, m - 2)) * x $$ (m - h - 1, 0))
    ∧ (∑h = 0..<m. of_int (N $$ (m - h - 1, m - 1)) * x $$ (m - h - 1, 0)) =
        c03*y0 + c13*y1 + c23*y2 + c33*y3 +
        (∑h = 4..<m. of_int (N $$ (m - h - 1, m - 1)) * x $$ (m - h - 1, 0))"
proof -
  have entries:
    "x $$ (m - 4,0) = x0"
    "x $$ (m - 3,0) = x1"
    "x $$ (m - 2,0) = x2"
    "x $$ (m - 1,0) = x3"
    using sparse_x_last_four_entries[OF m_props x_def] .

  have entries_rev:
    "x0 = x $$ (m - 4,0)"
    "x1 = x $$ (m - 3,0)"
    "x2 = x $$ (m - 2,0)"
    "x3 = x $$ (m - 1,0)"
    using entries by simp_all

  show ?thesis
    using brc_L0123_from_last_four[
      OF four_sq m_props(2) m_props(1)
         entries_rev(1) entries_rev(2) entries_rev(3) entries_rev(4)
         x0_eq x1_eq x2_eq x3_eq]
    .
qed

lemma brc_sparse_x_identity_and_coeffs:
  fixes a b c d m :: nat
  fixes y0 y1 y2 y3 x0 x1 x2 x3 :: rat
  fixes x :: "rat mat"
  assumes four_sq: "a^2 + b^2 + c^2 + d^2 = 𝗄 - Λ"
  assumes m_props: "m > 3" "𝗏 ≥ m"
  assumes x_def:
    "x = mat 𝗏 1 (λ(i,j).
        if j = 0 then
          (if i = m - 4 then x0
           else if i = m - 3 then x1
           else if i = m - 2 then x2
           else if i = m - 1 then x3
           else 0)
        else 0)"
  assumes x0_eq: "x0 = one_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x1_eq: "x1 = two_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x2_eq: "x2 = three_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x3_eq: "x3 = four_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  shows
   "(∑i∈{0..<𝗏}. (∑h∈{0..<𝗏}. of_int (N $$ (h,i)) * x $$ (h,0))^2)
    =
    of_int (int Λ) * (x0 + x1 + x2 + x3)^2
    + y0^2 + y1^2 + y2^2 + y3^2
    ∧
    (∃c00 c10 c20 c30 c01 c11 c21 c31 c02 c12 c22 c32 c03 c13 c23 c33.
      (∑h = 0..<m. of_int (N $$ (m - h - 1, m - 4)) * x $$ (m - h - 1, 0)) =
        c00*y0 + c10*y1 + c20*y2 + c30*y3 +
        (∑h = 4..<m. of_int (N $$ (m - h - 1, m - 4)) * x $$ (m - h - 1, 0))
    ∧ (∑h = 0..<m. of_int (N $$ (m - h - 1, m - 3)) * x $$ (m - h - 1, 0)) =
        c01*y0 + c11*y1 + c21*y2 + c31*y3 +
        (∑h = 4..<m. of_int (N $$ (m - h - 1, m - 3)) * x $$ (m - h - 1, 0))
    ∧ (∑h = 0..<m. of_int (N $$ (m - h - 1, m - 2)) * x $$ (m - h - 1, 0)) =
        c02*y0 + c12*y1 + c22*y2 + c32*y3 +
        (∑h = 4..<m. of_int (N $$ (m - h - 1, m - 2)) * x $$ (m - h - 1, 0))
    ∧ (∑h = 0..<m. of_int (N $$ (m - h - 1, m - 1)) * x $$ (m - h - 1, 0)) =
        c03*y0 + c13*y1 + c23*y2 + c33*y3 +
        (∑h = 4..<m. of_int (N $$ (m - h - 1, m - 1)) * x $$ (m - h - 1, 0)))"
proof -
  have id:
   "(∑i∈{0..<𝗏}. (∑h∈{0..<𝗏}. of_int (N $$ (h,i)) * x $$ (h,0))^2)
    =
    of_int (int Λ) * (x0 + x1 + x2 + x3)^2
    + y0^2 + y1^2 + y2^2 + y3^2"
    using brc_four_var_identity_for_sparse_x[
      OF four_sq m_props x_def x0_eq x1_eq x2_eq x3_eq] .

  have coeffs:
    "∃c00 c10 c20 c30 c01 c11 c21 c31 c02 c12 c22 c32 c03 c13 c23 c33.
      (∑h = 0..<m. of_int (N $$ (m - h - 1, m - 4)) * x $$ (m - h - 1, 0)) =
        c00*y0 + c10*y1 + c20*y2 + c30*y3 +
        (∑h = 4..<m. of_int (N $$ (m - h - 1, m - 4)) * x $$ (m - h - 1, 0))
    ∧ (∑h = 0..<m. of_int (N $$ (m - h - 1, m - 3)) * x $$ (m - h - 1, 0)) =
        c01*y0 + c11*y1 + c21*y2 + c31*y3 +
        (∑h = 4..<m. of_int (N $$ (m - h - 1, m - 3)) * x $$ (m - h - 1, 0))
    ∧ (∑h = 0..<m. of_int (N $$ (m - h - 1, m - 2)) * x $$ (m - h - 1, 0)) =
        c02*y0 + c12*y1 + c22*y2 + c32*y3 +
        (∑h = 4..<m. of_int (N $$ (m - h - 1, m - 2)) * x $$ (m - h - 1, 0))
    ∧ (∑h = 0..<m. of_int (N $$ (m - h - 1, m - 1)) * x $$ (m - h - 1, 0)) =
        c03*y0 + c13*y1 + c23*y2 + c33*y3 +
        (∑h = 4..<m. of_int (N $$ (m - h - 1, m - 1)) * x $$ (m - h - 1, 0))"
    using brc_sparse_x_L0123[
      OF four_sq m_props x_def x0_eq x1_eq x2_eq x3_eq] .

  show ?thesis
    using id coeffs by blast
qed

lemma brc_sparse_x_identity_exists:
  fixes a b c d m :: nat
  fixes y0 y1 y2 y3 :: rat
  assumes four_sq: "a^2 + b^2 + c^2 + d^2 = 𝗄 - Λ"
  assumes m_props: "m > 3" "𝗏 ≥ m"
  shows
   "∃(x :: rat mat) (x0 :: rat) (x1 :: rat) (x2 :: rat) (x3 :: rat).
      x = mat 𝗏 1 (λ(i,j).
        if j = 0 then
          (if i = m - 4 then x0
           else if i = m - 3 then x1
           else if i = m - 2 then x2
           else if i = m - 1 then x3
           else 0)
        else 0)
    ∧ x0 = one_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))
    ∧ x1 = two_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))
    ∧ x2 = three_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))
    ∧ x3 = four_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))
    ∧
      (∑i∈{0..<𝗏}. (∑h∈{0..<𝗏}. of_int (N $$ (h,i)) * x $$ (h,0))^2)
      =
      of_int (int Λ) * (x0 + x1 + x2 + x3)^2
      + y0^2 + y1^2 + y2^2 + y3^2"
proof -
  let ?x0 = "one_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  let ?x1 = "two_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  let ?x2 = "three_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  let ?x3 = "four_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  let ?X = "mat 𝗏 1 (λ(i,j).
        if j = 0 then
          (if i = m - 4 then ?x0
           else if i = m - 3 then ?x1
           else if i = m - 2 then ?x2
           else if i = m - 1 then ?x3
           else 0)
        else 0)"

  have Xdef:
    "?X = mat 𝗏 1 (λ(i,j).
        if j = 0 then
          (if i = m - 4 then ?x0
           else if i = m - 3 then ?x1
           else if i = m - 2 then ?x2
           else if i = m - 1 then ?x3
           else 0)
        else 0)"
    by simp

  have x0eq: "?x0 = one_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))" by simp
  have x1eq: "?x1 = two_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))" by simp
  have x2eq: "?x2 = three_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))" by simp
  have x3eq: "?x3 = four_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))" by simp

  have id:
    "(∑i∈{0..<𝗏}. (∑h∈{0..<𝗏}. of_int (N $$ (h,i)) * ?X $$ (h,0))^2)
      =
      of_int (int Λ) * (?x0 + ?x1 + ?x2 + ?x3)^2
      + y0^2 + y1^2 + y2^2 + y3^2"
    by (rule brc_four_var_identity_for_sparse_x[
        OF four_sq m_props Xdef x0eq x1eq x2eq x3eq])

  show ?thesis
    using id by blast
qed

lemma brc_simplified_to_y:
  fixes a b c d :: nat
  fixes x0 x1 x2 x3 y0 y1 y2 y3 :: rat
  assumes four_sq: "a^2 + b^2 + c^2 + d^2 = 𝗄 - Λ"
  assumes brc_simplified:
    "B =
       of_int (int Λ) * (x0 + x1 + x2 + x3)^2 +
       of_int (int (𝗄 - Λ)) * (x0^2 + x1^2 + x2^2 + x3^2)"
  assumes x0_eq: "x0 = one_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x1_eq: "x1 = two_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x2_eq: "x2 = three_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x3_eq: "x3 = four_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  shows
    "B =
       of_int (int Λ) * (x0 + x1 + x2 + x3)^2 +
       y0^2 + y1^2 + y2^2 + y3^2"
  using brc_simplified
        y_norm_replace_brc[OF four_sq x0_eq x1_eq x2_eq x3_eq]
  by simp

lemma sum_last_four:
  fixes f :: "nat ⇒ rat"
  assumes m4: "4 ≤ m"
  shows "(∑j = m - 4..<m. f j) =
    f (m - 4) + f (m - 3) + f (m - 2) + f (m - 1)"
proof -
  have a1: "Suc (m - 4) = m - 3"
    using m4 by simp
  have a2: "Suc (Suc (m - 4)) = m - 2"
    using m4 by simp
  have a3: "Suc (Suc (Suc (m - 4))) = m - 1"
    using m4 by simp

  have "(∑j = m - 4..<m. f j)
      = f (m - 4) + f (Suc (m - 4)) + f (Suc (Suc (m - 4))) +
        f (Suc (Suc (Suc (m - 4))))"
    using m4
    by (subst sum.atLeast_Suc_lessThan, simp_all)+

  then show ?thesis
    using a1 a2 a3
    by simp
qed

lemma sum_split_last_four:
  fixes f :: "nat ⇒ rat"
  assumes m4: "4 ≤ m"
  shows "(∑j = 0..<m. f j) =
    (∑j = 0..<m - 4. f j) +
    f (m - 4) + f (m - 3) + f (m - 2) + f (m - 1)"
proof -
  have split:
    "(∑j = 0..<m. f j) =
     (∑j = 0..<m - 4. f j) + (∑j = m - 4..<m. f j)"
    using m4 by (simp add: sum.atLeastLessThan_concat)
  also have "... =
     (∑j = 0..<m - 4. f j) +
     f (m - 4) + f (m - 3) + f (m - 2) + f (m - 1)"
    using sum_last_four[OF m4, of f]
    by (simp add: algebra_simps)
  finally show ?thesis .
qed

lemma sumsq_split_last_four:
  fixes f :: "nat ⇒ rat"
  assumes m4: "4 ≤ m"
  shows
   "(∑j = 0..<m. (f j)^2)
    =
    (∑j = 0..<m-4. (f j)^2)
    + (f (m - 4))^2
    + (f (m - 3))^2
    + (f (m - 2))^2
    + (f (m - 1))^2"
proof -
  have
   "(∑j = 0..<m. (f j)^2)
    =
    (∑j = 0..<m-4. (f j)^2)
    +
    (∑j = m-4..<m. (f j)^2)"
    using m4
    by (simp add: sum.atLeastLessThan_concat)

  also have
   "... =
    (∑j = 0..<m-4. (f j)^2)
    +
    ((f (m - 4))^2
     + (f (m - 3))^2
     + (f (m - 2))^2
     + (f (m - 1))^2)"
    using sum_last_four[OF m4, of "λj. (f j)^2"]
    by simp

  finally show ?thesis
    by (simp add: algebra_simps)
qed

lemma brc_linear_sum_split_last_four:
  fixes x :: "rat mat"
  assumes m4: "4 ≤ m"
  defines "L ≡ λj. ∑h∈{0..<𝗏}. of_int (N $$ (h,j)) * x $$ (h,0)"
  shows
   "(∑j = 0..<m. (L j)^2)
    =
    (∑j = 0..<m-4. (L j)^2)
    + (L (m - 4))^2
    + (L (m - 3))^2
    + (L (m - 2))^2
    + (L (m - 1))^2"
  using sumsq_split_last_four[OF m4, of L]
  by simp

lemma brc_linear_sum_split_last_four_expanded:
  fixes x :: "rat mat"
  assumes m4: "4 ≤ m"
  shows
   "(∑j = 0..<m.
      (∑h∈{0..<𝗏}. of_int (N $$ (h,j)) * x $$ (h,0))^2)
    =
    (∑j = 0..<m-4.
      (∑h∈{0..<𝗏}. of_int (N $$ (h,j)) * x $$ (h,0))^2)
    + (∑h∈{0..<𝗏}. of_int (N $$ (h,m-4)) * x $$ (h,0))^2
    + (∑h∈{0..<𝗏}. of_int (N $$ (h,m-3)) * x $$ (h,0))^2
    + (∑h∈{0..<𝗏}. of_int (N $$ (h,m-2)) * x $$ (h,0))^2
    + (∑h∈{0..<𝗏}. of_int (N $$ (h,m-1)) * x $$ (h,0))^2"
  using brc_linear_sum_split_last_four[OF m4, of x]
  by simp

definition brc_descent_invariant :: "nat ⇒ bool" where
  "brc_descent_invariant m ⟷
    (∃q0 q1 q2 :: rat.
      q0^2 =
        of_nat (𝗄 - Λ) * q1^2 +
        of_nat Λ * q2^2)"

definition brc_descent_form :: "nat ⇒ rat mat ⇒ rat ⇒ bool" where
  "brc_descent_form m x C ⟷
    C =
      (∑i∈{0..<m}.
        (∑h∈{0..<𝗏}. of_int (N $$ (h,i)) * x $$ (h,0))^2)"

definition brc_linear_form :: "rat mat ⇒ nat ⇒ rat" where
  "brc_linear_form x i =
    (∑h∈{0..<𝗏}. of_int (N $$ (h,i)) * x $$ (h,0))"

definition brc_square_sum_upto :: "nat ⇒ rat mat ⇒ rat" where
  "brc_square_sum_upto m x =
    (∑i∈{0..<m}. (brc_linear_form x i)^2)"

definition brc_tail_equation :: "nat ⇒ rat mat ⇒ rat ⇒ rat ⇒ bool" where
  "brc_tail_equation m x Y Z ⟷
    brc_square_sum_upto m x =
      of_nat Λ * Z^2 + Y"

lemma brc_tail_equationI:
  assumes
    "brc_square_sum_upto m x = of_nat Λ * Z^2 + Y"
  shows "brc_tail_equation m x Y Z"
  using assms
  unfolding brc_tail_equation_def
  by simp

lemma brc_tail_equationD:
  assumes "brc_tail_equation m x Y Z"
  shows "brc_square_sum_upto m x = of_nat Λ * Z^2 + Y"
  using assms
  unfolding brc_tail_equation_def
  by simp

lemma brc_tail_equation_full:
  fixes x :: "rat mat"
  shows
    "brc_tail_equation 𝗏 x
      (of_nat (𝗄 - Λ) * (∑j∈{0..<𝗏}. (x $$ (j,0))^2))
      (∑j∈{0..<𝗏}. x $$ (j,0))"
proof -
  have
    "brc_square_sum_upto 𝗏 x =
      of_nat Λ * (∑j∈{0..<𝗏}. x $$ (j,0))^2 +
      of_nat (𝗄 - Λ) * (∑j∈{0..<𝗏}. (x $$ (j,0))^2)"
    unfolding brc_square_sum_upto_def brc_linear_form_def
    using brc_x_equation[of x]
    by simp
  then show ?thesis
    unfolding brc_tail_equation_def
    by (simp add: algebra_simps)
qed

lemma brc_v_eq_4w_plus_1:
  assumes "𝗏 mod 4 = 1"
  shows "∃w. 𝗏 = 4 * w + 1"
proof
  show "𝗏 = 4 * (𝗏 div 4) + 1"
    using assms
    by (metis div_mult_mod_eq mult.commute)
qed

lemma brc_four_squares_k_minus_lambda:
  shows "∃a b c d :: nat. 𝗄 - Λ = a^2 + b^2 + c^2 + d^2"
proof -
  obtain a b c d :: nat where h:
    "a^2 + b^2 + c^2 + d^2 = 𝗄 - Λ"
    using four_squares_nat by blast
  have "𝗄 - Λ = a^2 + b^2 + c^2 + d^2"
    using h by simp
  then show ?thesis
    by blast
qed

(*lemma brc_v_1_mod_4:
  fixes a b c d m :: nat
  assumes four_sq: "a^2 + b^2 + c^2 + d^2 = 𝗄 - Λ"
  assumes m_props: "m > 3" "𝗏 ≥ m"
  assumes v_mod: "𝗏 mod 4 = 1"
  shows "∃x y z :: int. (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧
         of_int (x^2) = of_nat (𝗄 - Λ) * of_int (y^2) + of_nat Λ * of_int (z^2)"
proof -
  (* ------------------------------------------------------------------ *)
  (* 0. Set up arbitrary y' values and define x0..x3 via y_inv_of        *)
  (* ------------------------------------------------------------------ *)
  fix y0' y1' y2' y3' :: rat

  define x0 where "x0 = one_of   (y_inv_of ((a,b,c,d), y0', y1', y2', y3'))"
  define x1 where "x1 = two_of   (y_inv_of ((a,b,c,d), y0', y1', y2', y3'))"
  define x2 where "x2 = three_of (y_inv_of ((a,b,c,d), y0', y1', y2', y3'))"
  define x3 where "x3 = four_of  (y_inv_of ((a,b,c,d), y0', y1', y2', y3'))"

  (* x is an m×1 matrix, nonzero only in rows m-4..m-1 *)
  define x :: "rat mat" where
    "x = mat m 1 (λ(i,j).
        if j = 0 then
          (if i = m - 4 then x0
           else if i = m - 3 then x1
           else if i = m - 2 then x2
           else if i = m - 1 then x3
           else 0)
        else 0)"

  have m_ge4: "4 ≤ m" using m_props by simp

  (* handy inequalities / disequalities for simp *)
  have m4_lt_m: "m - 4 < m" using m_props by simp
  have m3_lt_m: "m - 3 < m" using m_props by simp
  have m2_lt_m: "m - 2 < m" using m_props by simp
  have m1_lt_m: "m - 1 < m" using m_props by simp
  have one_pos: "0 < (1::nat)" by simp

  have m3_ne_m4: "m - 3 ≠ m - 4" using m_props by simp
  have m2_ne_m4: "m - 2 ≠ m - 4" using m_props by simp
  have m2_ne_m3: "m - 2 ≠ m - 3" using m_props by simp
  have m1_ne_m4: "m - 1 ≠ m - 4" using m_props by simp
  have m1_ne_m3: "m - 1 ≠ m - 3" using m_props by simp
  have m1_ne_m2: "m - 1 ≠ m - 2" using m_props by simp

  (* exact values of the four special entries *)
  have x_at_m4: "x $$ (m - 4, 0) = x0"
    using x_def m_props m4_lt_m one_pos by simp
  have x_at_m3: "x $$ (m - 3, 0) = x1"
    using x_def m_props m3_lt_m one_pos m3_ne_m4 by simp
  have x_at_m2: "x $$ (m - 2, 0) = x2"
    using x_def m_props m2_lt_m one_pos m2_ne_m4 m2_ne_m3 by simp
  have x_at_m1: "x $$ (m - 1, 0) = x3"
    using x_def m_props m1_lt_m one_pos m1_ne_m4 m1_ne_m3 m1_ne_m2 by simp

  (* convenience equalities (often needed to match your library lemmas) *)
  have m3_ne_m4: "m - 3 ≠ m - 4" using m_props by simp
  have m2_ne_m4: "m - 2 ≠ m - 4" using m_props by simp
  have m2_ne_m3: "m - 2 ≠ m - 3" using m_props by simp
  have m1_ne_m4: "m - 1 ≠ m - 4" using m_props by simp
  have m1_ne_m3: "m - 1 ≠ m - 3" using m_props by simp
  have m1_ne_m2: "m - 1 ≠ m - 2" using m_props by simp

  (* ------------------------------------------------------------------ *)
  (* 1. THE IMPORTANT FIX: sums over x must use {m-4..<m}, not {0..<4}.   *)
  (*    First prove x is zero outside the last 4 rows (inside 0..<m).     *)
  (* ------------------------------------------------------------------ *)

  have x_zero_before_last4: "∀i<m-4. x $$ (i,0) = 0"
    unfolding x_def
    using m_props
    by auto

have x_zero_after_m: "∀i≥m. x $$ (i,0) = 0"
proof (intro allI impI)
  fix i assume hi: "i ≥ m"
  have out: "¬ (i < m ∧ 0 < (1::nat))"
    using hi by simp
  show "x $$ (i,0) = 0"
    unfolding x_def
    by (rule mat_index_outside_eq0[OF out])
qed



  (* Split {0..<𝗏} at m; the tail {m..<𝗏} is all zero *)
have sum_x_sq_tail_zero: "(∑j∈{m..<𝗏}. (x $$ (j,0))^2) = 0"
proof -
  have h0sq: "∀j∈{m..<𝗏}. (x $$ (j,0))^2 = 0"
    using x_zero_after_m by auto
  show ?thesis
    by (rule sum.eq_0) (use h0sq in auto)
qed

have sum_x_tail_zero: "(∑j∈{m..<𝗏}. x $$ (j,0)) = 0"
proof -
  have h0: "∀j∈{m..<𝗏}. x $$ (j,0) = 0"
    using x_zero_after_m by auto
  show ?thesis
    by (rule sum.eq_0) (use h0 in auto)
qed



have sum_x_tail_zero: "(∑j∈{m..<𝗏}. x $$ (j,0)) = 0"
proof -
  have h0: "∀j∈{m..<𝗏}. x $$ (j,0) = 0"
    using x_zero_after_m by auto
  show ?thesis
    by (rule sum.eq_0) (use h0 in auto)
qed

  (* Evaluate the {0..<m} sum: split at m-4 *)
  have sum_x_0_m: "(∑j∈{0..<m}. x $$ (j,0)) = x0 + x1 + x2 + x3"
  proof -
    have split0:
      "(∑j∈{0..<m}. x $$ (j,0))
       = (∑j∈{0..<m-4}. x $$ (j,0)) + (∑j∈{m-4..<m}. x $$ (j,0))"
      using m_ge4 by (simp add: sum.atLeastLessThan_concat)

    have first_zero: "(∑j∈{0..<m-4}. x $$ (j,0)) = 0"
    proof -
      have "∀j∈{0..<m-4}. x $$ (j,0) = 0"
        using x_zero_before_last4 by auto
      thus ?thesis by (simp add: sum.eq_zero)
    qed

    (* This simp lemma is in HOL: sum over a 4-length interval. *)
have last_four_expand:
  "(∑j∈{m-4..<m}. x $$ (j,0))
   = x $$ (m-4,0) + x $$ (m-3,0) + x $$ (m-2,0) + x $$ (m-1,0)"
proof -
  have h1: "m-1 < m" using m_ge4 by simp
  have h2: "m-2 < m-1" using m_ge4 by simp
  have h3: "m-3 < m-2" using m_ge4 by simp
  have h4: "m-4 < m-3" using m_ge4 by simp

  have A:
    "(∑j=m-4..<m. x $$ (j,0)) = (∑j=m-4..<m-1. x $$ (j,0)) + x $$ (m-1,0)"
    using h1 by (simp add: sum.atLeastLessThan_Suc)
  have B:
    "(∑j=m-4..<m-1. x $$ (j,0)) = (∑j=m-4..<m-2. x $$ (j,0)) + x $$ (m-2,0)"
    using h2 by (simp add: sum.atLeastLessThan_Suc)
  have C:
    "(∑j=m-4..<m-2. x $$ (j,0)) = (∑j=m-4..<m-3. x $$ (j,0)) + x $$ (m-3,0)"
    using h3 by (simp add: sum.atLeastLessThan_Suc)
  have D:
    "(∑j=m-4..<m-3. x $$ (j,0)) = (∑j=m-4..<m-4. x $$ (j,0)) + x $$ (m-4,0)"
    using h4 by (simp add: sum.atLeastLessThan_Suc)

  from A B C D show ?thesis
    by (simp add: algebra_simps)
qed


  have sum_x_sq_0_m: "(∑j∈{0..<m}. (x $$ (j,0))^2) = x0^2 + x1^2 + x2^2 + x3^2"
  proof -
    have split0:
      "(∑j∈{0..<m}. (x $$ (j,0))^2)
       = (∑j∈{0..<m-4}. (x $$ (j,0))^2) + (∑j∈{m-4..<m}. (x $$ (j,0))^2)"
      using m_ge4 by (simp add: sum.atLeastLessThan_concat)

    have first_zero: "(∑j∈{0..<m-4}. (x $$ (j,0))^2) = 0"
    proof -
      have "∀j∈{0..<m-4}. (x $$ (j,0))^2 = 0"
        using x_zero_before_last4 by auto
      thus ?thesis by (simp add: sum.eq_zero)
    qed

    have last_four:
      "(\<Sum>j = m-4..<m. x $$ (j,0)) = x0 + x1 + x2 + x3"
      using last_four_expand x_at_m4 x_at_m3 x_at_m2 x_at_m1
      by simp

    show ?thesis using split0 first_zero last_four by simp
  qed

  (* Now assemble sums over {0..<𝗏} using {0..<m} ∪ {m..<𝗏} *)
  have split_v_m: "{0..<𝗏} = {0..<m} ∪ {m..<𝗏}"
    using m_props by auto
  have inter_v_m: "{0..<m} ∩ {m..<𝗏} = {}"
    by auto

  have sum_x_simple: "(∑j∈{0..<𝗏}. x $$ (j,0)) = x0 + x1 + x2 + x3"
  proof -
    have fin0: "finite ({0..<m} :: nat set)" by simp
    have fin1: "finite ({m..<𝗏} :: nat set)" by simp
    have disj: "{0..<m} ∩ {m..<𝗏} = {}" using inter_v_m by simp
    have un: "{0..<𝗏} = {0..<m} ∪ {m..<𝗏}" using split_v_m by simp
    have
      "(∑j∈{0..<𝗏}. x $$ (j,0))
       = (∑j∈{0..<m}. x $$ (j,0)) + (∑j∈{m..<𝗏}. x $$ (j,0))"
      using sum.union_disjoint[OF fin0 fin1 disj, of "λj. x $$ (j,0)"] un
      by simp
    thus ?thesis using sum_x_0_m sum_x_tail_zero by simp
  qed

  have sum_x_sq_simple: "(∑j∈{0..<𝗏}. (x $$ (j,0))^2) = x0^2 + x1^2 + x2^2 + x3^2"
  proof -
    have fin0: "finite ({0..<m} :: nat set)" by simp
    have fin1: "finite ({m..<𝗏} :: nat set)" by simp
    have disj: "{0..<m} ∩ {m..<𝗏} = {}" using inter_v_m by simp
    have un: "{0..<𝗏} = {0..<m} ∪ {m..<𝗏}" using split_v_m by simp
    have
      "(∑j∈{0..<𝗏}. (x $$ (j,0))^2)
       = (∑j∈{0..<m}. (x $$ (j,0))^2) + (∑j∈{m..<𝗏}. (x $$ (j,0))^2)"
      using sum.union_disjoint[OF fin0 fin1 disj, of "λj. (x $$ (j,0))^2"] un
      by simp
    thus ?thesis using sum_x_sq_0_m sum_x_sq_tail_zero by simp
  qed

  (* ------------------------------------------------------------------ *)
  (* 2. Your linear-combination lemmas (keep them), but DO NOT re-obtain  *)
  (*    e00 e10 ... multiple times with the same names. Use distinct names *)
  (*    per column to prevent shadowing.                                  *)
  (* ------------------------------------------------------------------ *)

  have i0_in: "(0::nat) ∈ {0..<4}" by simp
  have i1_in: "(1::nat) ∈ {0..<4}" by simp
  have i2_in: "(2::nat) ∈ {0..<4}" by simp
  have i3_in: "(3::nat) ∈ {0..<4}" by simp

  (* Column m-4 coefficients *)
  have ex_col_m4:
    "∃c00 c10 c20 c30.
      (∑h = 0..<m. rat_of_int (N $$ (m - h - 1, m - 4)) * x $$ (m - h - 1, 0)) =
        c00*y0' + c10*y1' + c20*y2' + c30*y3' +
      (∑h = 4..<m. rat_of_int (N $$ (m - h - 1, m - 4)) * x $$ (m - h - 1, 0))"
    using linear_comb_of_y_part_2[OF four_sq m_props(2) m_props(1) i3_in
          x0_eq x1_eq x2_eq x3_eq x0_def x1_def x2_def x3_def]
    by blast

  obtain c00 c10 c20 c30 where Li_m4:
    "(∑h = 0..<m. rat_of_int (N $$ (m - h - 1, m - 4)) * x $$ (m - h - 1, 0)) =
        c00*y0' + c10*y1' + c20*y2' + c30*y3' +
      (∑h = 4..<m. rat_of_int (N $$ (m - h - 1, m - 4)) * x $$ (m - h - 1, 0))"
    using ex_col_m4 by blast

  (* Column m-3 coefficients *)
  have ex_col_m3:
    "∃c01 c11 c21 c31.
      (∑h = 0..<m. rat_of_int (N $$ (m - h - 1, m - 3)) * x $$ (m - h - 1, 0)) =
        c01*y0' + c11*y1' + c21*y2' + c31*y3' +
      (∑h = 4..<m. rat_of_int (N $$ (m - h - 1, m - 3)) * x $$ (m - h - 1, 0))"
    using linear_comb_of_y_part_2[OF four_sq m_props(2) m_props(1) i2_in
          x0_eq x1_eq x2_eq x3_eq x0_def x1_def x2_def x3_def]
    by blast

  obtain c01 c11 c21 c31 where Li_m3:
    "(∑h = 0..<m. rat_of_int (N $$ (m - h - 1, m - 3)) * x $$ (m - h - 1, 0)) =
        c01*y0' + c11*y1' + c21*y2' + c31*y3' +
      (∑h = 4..<m. rat_of_int (N $$ (m - h - 1, m - 3)) * x $$ (m - h - 1, 0))"
    using ex_col_m3 by blast

  (* Column m-2 coefficients *)
  have ex_col_m2:
    "∃c02 c12 c22 c32.
      (∑h = 0..<m. rat_of_int (N $$ (m - h - 1, m - 2)) * x $$ (m - h - 1, 0)) =
        c02*y0' + c12*y1' + c22*y2' + c32*y3' +
      (∑h = 4..<m. rat_of_int (N $$ (m - h - 1, m - 2)) * x $$ (m - h - 1, 0))"
    using linear_comb_of_y_part_2[OF four_sq m_props(2) m_props(1) i1_in
          x0_eq x1_eq x2_eq x3_eq x0_def x1_def x2_def x3_def]
    by blast

  obtain c02 c12 c22 c32 where Li_m2:
    "(∑h = 0..<m. rat_of_int (N $$ (m - h - 1, m - 2)) * x $$ (m - h - 1, 0)) =
        c02*y0' + c12*y1' + c22*y2' + c32*y3' +
      (∑h = 4..<m. rat_of_int (N $$ (m - h - 1, m - 2)) * x $$ (m - h - 1, 0))"
    using ex_col_m2 by blast

  (* Column m-1 coefficients *)
  have ex_col_m1:
    "∃c03 c13 c23 c33.
      (∑h = 0..<m. rat_of_int (N $$ (m - h - 1, m - 1)) * x $$ (m - h - 1, 0)) =
        c03*y0' + c13*y1' + c23*y2' + c33*y3' +
      (∑h = 4..<m. rat_of_int (N $$ (m - h - 1, m - 1)) * x $$ (m - h - 1, 0))"
    using linear_comb_of_y_part_2[OF four_sq m_props(2) m_props(1) i0_in
          x0_eq x1_eq x2_eq x3_eq x0_def x1_def x2_def x3_def]
    by blast

  obtain c03 c13 c23 c33 where Li_m1:
    "(∑h = 0..<m. rat_of_int (N $$ (m - h - 1, m - 1)) * x $$ (m - h - 1, 0)) =
        c03*y0' + c13*y1' + c23*y2' + c33*y3' +
      (∑h = 4..<m. rat_of_int (N $$ (m - h - 1, m - 1)) * x $$ (m - h - 1, 0))"
    using ex_col_m1 by blast

  (* ------------------------------------------------------------------ *)
  (* 3. Define L0..L3 using your intended “left+tail” structure.          *)
  (*    (Keep your versions; here is the clean form with rats.)           *)
  (* ------------------------------------------------------------------ *)

  define L0 where
    "L0 =
      (∑h = 0..<m. rat_of_int (N $$ (m - h - 1, m - 4)) * x $$ (m - h - 1, 0))
    + (∑h = m..<𝗏. rat_of_int (N $$ (h, m - 4)) * x $$ (h, 0))"

  define L1 where
    "L1 =
      (∑h = 0..<m. rat_of_int (N $$ (m - h - 1, m - 3)) * x $$ (m - h - 1, 0))
    + (∑h = m..<𝗏. rat_of_int (N $$ (h, m - 3)) * x $$ (h, 0))"

  define L2 where
    "L2 =
      (∑h = 0..<m. rat_of_int (N $$ (m - h - 1, m - 2)) * x $$ (m - h - 1, 0))
    + (∑h = m..<𝗏. rat_of_int (N $$ (h, m - 2)) * x $$ (h, 0))"

  define L3 where
    "L3 =
      (∑h = 0..<m. rat_of_int (N $$ (m - h - 1, m - 1)) * x $$ (m - h - 1, 0))
    + (∑h = m..<𝗏. rat_of_int (N $$ (h, m - 1)) * x $$ (h, 0))"

  (* ------------------------------------------------------------------ *)
  (* 4. State brc_x_equation in the simplified form using the fixed sums. *)
  (* ------------------------------------------------------------------ *)

  have brc:
    "(∑i ∈ {0..<𝗏}. (∑h ∈ {0..<𝗏}. of_int (N $$ (h,i)) * x $$ (h,0))^2) =
       of_int (int Λ) * (∑j ∈ {0..<𝗏}. x $$ (j, 0))^2 +
       of_int (int (𝗄 - Λ)) * (∑j ∈ {0..<𝗏}. (x $$ (j, 0))^2)"
    using brc_x_equation by auto

  have brc_simplified:
    "(∑i ∈ {0..<𝗏}. (∑h ∈ {0..<𝗏}. of_int (N $$ (h,i)) * x $$ (h,0))^2) =
       of_int (int Λ) * (x0 + x1 + x2 + x3)^2 +
       of_int (int (𝗄 - Λ)) * (x0^2 + x1^2 + x2^2 + x3^2)"
    using brc sum_x_simple sum_x_sq_simple
    by simp

  (* ------------------------------------------------------------------ *)
  (* 5. Everything after this depends on your existing library:           *)
  (*    - relate x0..x3 to y0'..y3' via y_inv_of / lagrange identity      *)
  (*    - define y0..y3 via elimination so that yk^2 = Lk^2               *)
  (*    - show L0^2+L1^2+L2^2+L3^2 equals the corresponding piece of the  *)
  (*      big sum over i, then derive the Pell-style integer equation.     *)
  (* ------------------------------------------------------------------ *)

  (* At this point you continue with your existing “y_of / lagrange_trans” block,
     but NOW the broken indexing (first_four / {0..<4} for x) is gone.

     The final line is left as in your original: *)
  show ?thesis
    sorry
qed*)

end
end
