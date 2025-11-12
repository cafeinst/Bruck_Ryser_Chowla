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

lemma brc_recursive_elimination:
  fixes a b c d m :: nat
  fixes x :: "rat mat"
  assumes four_sq: "a^2 + b^2 + c^2 + d^2 = 𝗄 - Λ"
  assumes m_props: "m ≥ 1" "𝗏 ≥ m" "m mod 4 = 1"
  assumes brc_eq: "(∑i ∈ {0..<m}. (∑h ∈ {0..<m}. of_int(N $$ (h,i)) * x $$ (h,0))^2) =
                   of_int Λ * (∑j ∈ {0..<m}. x $$ (j,0))^2 + 
                   of_int(𝗄-Λ) * (∑j ∈ {0..<m}. (x $$ (j,0))^2)"
  shows "∃s t :: rat. s^2 = of_int Λ * t^2 + of_int(𝗄-Λ) ∧ (s ≠ 0 ∨ t ≠ 0)"
  using m_props
proof (induction m rule: less_induct)
  case (less m)
  
  (* Base case: m = 1 *)
  have base_case: "m = 1 ⟹ ?thesis"
  proof -
    assume m_eq_1: "m = 1"
    
    (* When m = 1, the equation simplifies *)
    have "(∑i ∈ {0..<1}. (∑h ∈ {0..<1}. of_int(N $$ (h,i)) * x $$ (h,0))^2) =
          of_int Λ * (∑j ∈ {0..<1}. x $$ (j,0))^2 + 
          of_int(𝗄-Λ) * (∑j ∈ {0..<1}. (x $$ (j,0))^2)"
      using brc_eq m_eq_1 by simp
    
    (* Simplify: sums over {0..<1} have only one term *)
    then have "(of_int(N $$ (0,0)) * x $$ (0,0))^2 =
               of_int Λ * (x $$ (0,0))^2 + of_int(𝗄-Λ) * (x $$ (0,0))^2"
      by simp
    
    then have "(of_int(N $$ (0,0)) * x $$ (0,0))^2 =
               (of_int Λ + of_int(𝗄-Λ)) * (x $$ (0,0))^2"
      by (simp add: algebra_simps)
    
    have "of_int Λ + of_int(𝗄-Λ) = of_int(int 𝗄)"
      using blocksize_gt_index by (simp add: of_nat_diff)
    
    then have "(of_int(N $$ (0,0)) * x $$ (0,0))^2 = of_int(int 𝗄) * (x $$ (0,0))^2"
      using `(of_int(N $$ (0,0)) * x $$ (0,0))^2 = (of_int Λ + of_int(𝗄-Λ)) * (x $$ (0,0))^2`
      by simp
    
    (* Case split on whether x $$ (0,0) = 0 *)
    show ?thesis
    proof (cases "x $$ (0,0) = 0")
      case True
      (* If x(0,0) = 0, then N(0,0) * 0 = 0, so we have 0 = 0 *)
      (* We need a non-trivial solution, so pick s = sqrt(k-λ), t = 0 *)
      define s :: rat where "s = 1"
      define t :: rat where "t = 0"
      
      have "s^2 = of_int Λ * t^2 + of_int(𝗄-Λ)"
        unfolding s_def t_def by simp
      moreover have "s ≠ 0 ∨ t ≠ 0"
        unfolding s_def t_def by simp
      ultimately show ?thesis by blast
    next
      case False
      (* If x(0,0) ≠ 0, divide both sides by (x(0,0))^2 *)
      have "(of_int(N $$ (0,0)))^2 = of_int(int 𝗄)"
        using `(of_int(N $$ (0,0)) * x $$ (0,0))^2 = of_int(int 𝗄) * (x $$ (0,0))^2`
              False
        by (simp add: power2_eq_square power_mult_distrib)
      
      (* Extract s and t *)
      define s :: rat where "s = of_int(N $$ (0,0))"
      define t :: rat where "t = 0"
      
      (* We have s^2 = k = λ + (k-λ) = λ*0 + (k-λ)*1 *)
      have "s^2 = of_int(int 𝗄)"
        unfolding s_def using `(of_int(N $$ (0,0)))^2 = of_int(int 𝗄)` by simp
      
      then have "s^2 = of_int Λ + of_int(𝗄-Λ)"
        using blocksize_gt_index by (simp add: of_nat_diff)
      
      then have "s^2 = of_int Λ * 1 + of_int(𝗄-Λ) * 1"
        by simp
      
      (* This gives us the form s^2 = λ*t^2 + (k-λ) if we set t appropriately *)
      (* Actually, we have s^2 = k, so s^2 - (k-λ) = λ *)
      (* So s^2 = λ + (k-λ) = λ*1^2 + (k-λ) *)
      
      (* Rewrite to match the Pell form *)
      have "s^2 = of_int Λ * t^2 + of_int(𝗄-Λ)"
        unfolding t_def using `s^2 = of_int Λ + of_int(𝗄-Λ)` by simp
      
      moreover have "s ≠ 0 ∨ t ≠ 0"
        unfolding s_def t_def by simp
      
      ultimately show ?thesis by blast
    qed
  qed
  
  (* Recursive case: m > 1 *)
  have recursive_case: "m > 1 ⟹ ?thesis"
  proof -
    assume "m > 1"
    then have "m ≥ 5" using less.prems(3) by auto
    then have m_gt_4: "m > 4" by simp
    
    (* Do the elimination step as in your original proof *)
    (* Extract last 4 variables *)
    define x0 where "x0 = x $$ (m-4, 0)"
    define x1 where "x1 = x $$ (m-3, 0)"
    define x2 where "x2 = x $$ (m-2, 0)"
    define x3 where "x3 = x $$ (m-1, 0)"
    
    (* Apply linear_comb_of_y_part_1 to get the structure *)
    (* ... all your Li0-Li3 code ... *)
    
    (* Define y0, y1, y2, y3 using elimination *)
    (* ... all your y definitions ... *)
    
    (* Key: show that we get an equation for m-4 variables *)
    (* This would use your lagrange_identity_y and sum manipulations *)
    
    have "∃x'. (∑i ∈ {0..<m-4}. (∑h ∈ {0..<m-4}. of_int(N $$ (h,i)) * x' $$ (h,0))^2) =
               of_int Λ * (∑j ∈ {0..<m-4}. x' $$ (j,0))^2 + 
               of_int(𝗄-Λ) * (∑j ∈ {0..<m-4}. (x' $$ (j,0))^2)"
      sorry (* This is the elimination step - uses your existing machinery *)
    
    then obtain x' where x'_eq:
      "(∑i ∈ {0..<m-4}. (∑h ∈ {0..<m-4}. of_int(N $$ (h,i)) * x' $$ (h,0))^2) =
       of_int Λ * (∑j ∈ {0..<m-4}. x' $$ (j,0))^2 + 
       of_int(𝗄-Λ) * (∑j ∈ {0..<m-4}. (x' $$ (j,0))^2)"
      by blast
    
    (* Apply induction hypothesis *)
    have "m - 4 < m" using m_gt_4 by simp
    moreover have "m - 4 ≥ 1" using m_gt_4 less.prems(3) by auto
    moreover have "(m - 4) mod 4 = 1" using less.prems(3) by auto
    moreover have "𝗏 ≥ m - 4" using less.prems(2) by simp
    
    ultimately show ?thesis
      using less.IH[of "m-4" x'] four_sq x'_eq by simp
  qed
  
  show ?thesis
    using base_case recursive_case by (cases "m = 1") auto
qed

(*lemma brc_v_1_mod_4:
  fixes a b c d m :: nat
  assumes four_sq: "a^2 + b^2 + c^2 + d^2 = 𝗄 - Λ"
  assumes m_props: "m > 3" "𝗏 ≥ m"
  assumes v_mod: "𝗏 mod 4 = 1"
  shows "∃x y z :: int. (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧
         of_int(x^2) = of_nat(𝗄 - Λ) * of_int(y^2) + of_nat Λ * of_int(z^2)"
proof -
  (* Start with arbitrary y-values to get coefficients *)
  fix y0' y1' y2' y3' :: rat
  
  (* Define x-values from y-values using y_inv_of *)
  define x0 where "x0 = one_of(y_inv_of((a, b, c, d), (y0', y1', y2', y3')))"
  define x1 where "x1 = two_of(y_inv_of((a, b, c, d), (y0', y1', y2', y3')))"
  define x2 where "x2 = three_of(y_inv_of((a, b, c, d), (y0', y1', y2', y3')))"
  define x3 where "x3 = four_of(y_inv_of((a, b, c, d), (y0', y1', y2', y3')))"
  
  define x :: "rat mat" where "x = mat m 1 (λ(i, j).
     if j = 0 then
       if i = m - 4 then x0
       else if i = m - 3 then x1
       else if i = m - 2 then x2
       else if i = m - 1 then x3
       else 0
     else 0)"
  
  (* Establish x matrix indexing *)
  have "0 < (1::nat)" by simp
  have "m - 4 < m" using m_props by simp
  have "m - 3 < m" using m_props by simp
  have "m - 2 < m" using m_props by simp
  have "m - 1 < m" using m_props by simp
  
  have "m - 3 ≠ m - 4" using m_props by simp
  have "m - 2 ≠ m - 4" using m_props by simp
  have "m - 2 ≠ m - 3" using m_props by simp
  have "m - 1 ≠ m - 4" using m_props by simp
  have "m - 1 ≠ m - 3" using m_props by simp
  have "m - 1 ≠ m - 2" using m_props by simp
  
  have x_at_m4: "x $$ (m - 4, 0) = x0"
    using x_def m_props `m - 4 < m` `0 < 1` by simp
  
  have x_at_m3: "x $$ (m - 3, 0) = x1"
    using x_def m_props `m - 3 < m` `0 < 1` `m - 3 ≠ m - 4` by simp
  
  have x_at_m2: "x $$ (m - 2, 0) = x2"
    using x_def m_props `m - 2 < m` `0 < 1` `m - 2 ≠ m - 4` `m - 2 ≠ m - 3` by simp
  
  have x_at_m1: "x $$ (m - 1, 0) = x3"
    using x_def m_props `m - 1 < m` `0 < 1` `m - 1 ≠ m - 4` `m - 1 ≠ m - 3` `m - 1 ≠ m - 2` by simp

  have i0_in: "(0::nat) ∈ {0..<4}" by simp
  have i1_in: "(1::nat) ∈ {0..<4}" by simp
  have i2_in: "(2::nat) ∈ {0..<4}" by simp
  have i3_in: "(3::nat) ∈ {0..<4}" by simp

  have "∃e0 e1 e2 e3. (∑h ∈ {0..<m}. of_int(N $$ (m-h-1,m-0-1)) * x $$ (m-h-1,0)) = 
                      e0 * y0' + e1 * y1' + e2 * y2' + e3 * y3' +
                      (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-0-1)) * x $$ (m-h-1,0))"
    using linear_comb_of_y_part_2 four_sq m_props i0_in x_at_m4 x_at_m3 x_at_m2 x_at_m1
        x0_def x1_def x2_def x3_def
    by blast
  then obtain e00 e10 e20 e30 where Li0:
    "(∑h ∈ {0..<m}. of_int(N $$ (m-h-1,m-0-1)) * x $$ (m-h-1,0)) = 
    e00 * y0' + e10 * y1' + e20 * y2' + e30 * y3' +
    (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-0-1)) * x $$ (m-h-1,0))"
    by blast

  have "∃e0 e1 e2 e3. (∑h ∈ {0..<m}. of_int(N $$ (m-h-1,m-1-1)) * x $$ (m-h-1,0)) = 
                      e0 * y0' + e1 * y1' + e2 * y2' + e3 * y3' +
                      (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-1-1)) * x $$ (m-h-1,0))"
    using linear_comb_of_y_part_2 four_sq m_props i1_in x_at_m4 x_at_m3 x_at_m2 x_at_m1
        x0_def x1_def x2_def x3_def
    by blast
  then obtain e01 e11 e21 e31 where Li1:
    "(∑h ∈ {0..<m}. of_int(N $$ (m-h-1,m-1-1)) * x $$ (m-h-1,0)) = 
    e01 * y0' + e11 * y1' + e21 * y2' + e31 * y3' +
    (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-1-1)) * x $$ (m-h-1,0))"
    by blast

  have "∃e0 e1 e2 e3. (∑h ∈ {0..<m}. of_int(N $$ (m-h-1,m-2-1)) * x $$ (m-h-1,0)) = 
                      e0 * y0' + e1 * y1' + e2 * y2' + e3 * y3' +
                      (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-2-1)) * x $$ (m-h-1,0))"
    using linear_comb_of_y_part_2 four_sq m_props i2_in x_at_m4 x_at_m3 x_at_m2 x_at_m1
        x0_def x1_def x2_def x3_def
    by blast
  then obtain e02 e12 e22 e32 where Li2:
    "(∑h ∈ {0..<m}. of_int(N $$ (m-h-1,m-2-1)) * x $$ (m-h-1,0)) = 
    e02 * y0' + e12 * y1' + e22 * y2' + e32 * y3' +
    (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-2-1)) * x $$ (m-h-1,0))"
    by blast

  have "∃e0 e1 e2 e3. (∑h ∈ {0..<m}. of_int(N $$ (m-h-1,m-3-1)) * x $$ (m-h-1,0)) = 
                      e0 * y0' + e1 * y1' + e2 * y2' + e3 * y3' +
                      (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-3-1)) * x $$ (m-h-1,0))"
    using linear_comb_of_y_part_2 four_sq m_props i3_in x_at_m4 x_at_m3 x_at_m2 x_at_m1
        x0_def x1_def x2_def x3_def
    by blast
  then obtain e03 e13 e23 e33 where Li3:
    "(∑h ∈ {0..<m}. of_int(N $$ (m-h-1,m-3-1)) * x $$ (m-h-1,0)) = 
    e03 * y0' + e13 * y1' + e23 * y2' + e33 * y3' +
    (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-3-1)) * x $$ (m-h-1,0))"
    by blast

  (* Now redefine y-values using those coefficients *)
  define y0 where "y0 = (if e00 = 1 then 
    -(e10 * y1' + e20 * y2' + e30 * y3' +
      (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
      (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-4)) * x $$ (h,0)))/2 
    else  
      (e10 * y1' + e20 * y2' + e30 * y3' +
      (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
      (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-4)) * x $$ (h,0)))/(1-e00))"
      
  define y1 where "y1 = (if e11 = 1 then 
    -(e01 * y0' + e21 * y2' + e31 * y3' +
      (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
      (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-3)) * x $$ (h,0)))/2 
    else  
      (e01 * y0' + e21 * y2' + e31 * y3' +
      (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
      (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-3)) * x $$ (h,0)))/(1-e11))"
      
  define y2 where "y2 = (if e22 = 1 then 
    -(e02 * y0' + e12 * y1' + e32 * y3' +
      (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
      (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-2)) * x $$ (h,0)))/2 
    else  
      (e02 * y0' + e12 * y1' + e32 * y3' +
      (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
      (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-2)) * x $$ (h,0)))/(1-e22))"
      
  define y3 where "y3 = (if e33 = 1 then 
    -(e03 * y0' + e13 * y1' + e23 * y2' +
      (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
      (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-1)) * x $$ (h,0)))/2 
    else  
      (e03 * y0' + e13 * y1' + e23 * y2' +
      (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
      (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-1)) * x $$ (h,0)))/(1-e33))"

  (* Define the L's *)
  define L0 where "L0 = (∑h ∈ {0..<m}. of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
                        (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-4)) * x $$ (h,0))"
  define L1 where "L1 = (∑h ∈ {0..<m}. of_int(N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
                        (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-3)) * x $$ (h,0))"
  define L2 where "L2 = (∑h ∈ {0..<m}. of_int(N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
                        (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-2)) * x $$ (h,0))"
  define L3 where "L3 = (∑h ∈ {0..<m}. of_int(N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
                        (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-1)) * x $$ (h,0))"

  (* Key algebra: split the sum *)
  have sumdef: "(∑j ∈ {0..<4}.((∑h ∈ {0..<m}. of_int(N $$ (m-h-1,m-j-1)) * x $$ (m-h-1,0)) +
                 (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-j-1)) * x $$ (h,0)))^2) = 
                  L0^2 + L1^2 + L2^2 + L3^2"
     unfolding L0_def L1_def L2_def L3_def
     by (simp add: numeral.simps(2,3))

  have split1: "{0..<m} = {0..<4} ∪ {4..<m}" using m_props by auto
  have inter1: "{0..<4} ∩ {4..<m} = {}" by auto
  
  have trick1: "(∑j ∈ {0..<m}. ((∑h ∈ {0..<m}. of_int(N $$ (m-h-1,m-j-1)) * x $$ (m-h-1,0)) +
                 (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-j-1)) * x $$ (h,0)))^2) =
        (∑j ∈ {0..<4}. ((∑h ∈ {0..<m}. of_int(N $$ (m-h-1,m-j-1)) * x $$ (m-h-1,0)) +
                 (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-j-1)) * x $$ (h,0)))^2) + 
        (∑j ∈ {4..<m}. ((∑h ∈ {0..<m}. of_int(N $$ (m-h-1,m-j-1)) * x $$ (m-h-1,0)) +
                 (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-j-1)) * x $$ (h,0)))^2)"
  proof -
    have "finite ({0..<4} :: nat set)" by simp
    have "finite ({4..<m} :: nat set)" by simp
    have "{0..<4} ∩ {4..<m} = {}" using inter1 by simp
    have "{0..<m} = {0..<4} ∪ {4..<m}" using split1 by simp
    show ?thesis
      using sum.union_disjoint[OF `finite {0..<4}` `finite {4..<m}` `{0..<4} ∩ {4..<m} = {}`,
          of "λj. ((∑h ∈ {0..<m}. of_int(N $$ (m-h-1,m-j-1)) * x $$ (m-h-1,0)) +
                   (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-j-1)) * x $$ (h,0)))^2"]
          `{0..<m} = {0..<4} ∪ {4..<m}` by simp
  qed
    
  then have lhs: "(∑j ∈ {0..<m}. ((∑h ∈ {0..<m}. of_int(N $$ (m-h-1,m-j-1)) * x $$ (m-h-1,0)) +
                  (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-j-1)) * x $$ (h,0)))^2) =
                  L0^2 + L1^2 + L2^2 + L3^2 + 
                  (∑j ∈ {4..<m}. ((∑h ∈ {0..<m}. of_int(N $$ (m-h-1,m-j-1)) * x $$ (m-h-1,0)) +
                  (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-j-1)) * x $$ (h,0)))^2)"
    using sumdef by algebra

  (* From brc_x_equation *)
  have brc: "(∑i ∈ {0..<𝗏}.(∑h ∈ {0..<𝗏}. of_int (N $$ (h,i)) * x $$ (h,0))^2) =
     of_int (int Λ) * (∑j ∈ {0..<𝗏}.(x $$ (j, 0)))^2 +
     of_int (int (𝗄 - Λ)) * (∑j ∈ {0..<𝗏}. (x $$ (j, 0))^2)"
    using brc_x_equation by auto

  (* Split on RHS *)
  have split2: "{0..<𝗏} = {0..<4} ∪ {4..<𝗏}" using m_props by auto
  have inter2: "{0..<4} ∩ {4..<𝗏} = {}" by auto
  
  have x_split: "(∑j ∈ {0..<𝗏}. (x $$ (j, 0))^2) =
                 (∑j ∈ {0..<4}. (x $$ (j, 0))^2) +
                 (∑j ∈ {4..<𝗏}. (x $$ (j, 0))^2)"
  proof -
    have "finite ({0..<4} :: nat set)" by simp
    have "finite ({4..<𝗏} :: nat set)" by simp
    show ?thesis
      using sum.union_disjoint[OF `finite {0..<4}` `finite {4..<𝗏}` inter2,
          of "λj. (x $$ (j, 0))^2"]
      using split2 by simp
  qed

  (* Key: x $$ (j, 0) for j < 4 corresponds to xj from transformation *)
  have first_four: "(∑j ∈ {0..<4}. (x $$ (j, 0))^2) = 
                    x $$ (m-4, 0)^2 + x $$ (m-3, 0)^2 + x $$ (m-2, 0)^2 + x $$ (m-1, 0)^2"
    sorry (* Need to show indices match up *)

  have "y_of((a, b, c, d),(x0, x1, x2, x3)) = (y0', y1', y2', y3')"
  proof -
    have nz: "a^2 + b^2 + c^2 + d^2 ≠ 0"
      using four_sq blocksize_gt_index by simp
  
  (* Extract the tuple from y_inv_of *)
    have x_tuple: "(x0, x1, x2, x3) = y_inv_of((a, b, c, d),(y0', y1', y2', y3'))"
      unfolding x0_def x1_def x2_def x3_def by simp
  
  (* y_inv_of extracts snd of y_inv_reversible *)
    have "y_inv_of((a, b, c, d),(y0', y1', y2', y3')) = 
        snd(y_inv_reversible((a, b, c, d),(y0', y1', y2', y3')))"
      by simp
  
  (* Use y_inverses_part_2 *)
    have inv2: "y_reversible(y_inv_reversible((a, b, c, d),(y0', y1', y2', y3'))) = 
              ((a, b, c, d),(y0', y1', y2', y3'))"
      using y_inverses_part_2[OF nz] by simp
  
  (* Take snd of both sides *)
    have "snd(y_reversible(y_inv_reversible((a, b, c, d),(y0', y1', y2', y3')))) = 
        snd(((a, b, c, d),(y0', y1', y2', y3')))"
      using inv2 by simp
    then have "snd(y_reversible(y_inv_reversible((a, b, c, d),(y0', y1', y2', y3')))) = 
             (y0', y1', y2', y3')"
      by simp
  
  (* Now connect to y_of *)
    have "y_of((a, b, c, d), snd(y_inv_reversible((a, b, c, d),(y0', y1', y2', y3')))) =
        snd(y_reversible((a, b, c, d), snd(y_inv_reversible((a, b, c, d),(y0', y1', y2', y3')))))"
      by simp
  
  (* Use the fact that y_inv_reversible returns a pair *)
    moreover have "y_reversible((a, b, c, d), snd(y_inv_reversible((a, b, c, d),(y0', y1', y2', y3')))) =
                 y_reversible(y_inv_reversible((a, b, c, d),(y0', y1', y2', y3')))"
      by (cases "y_inv_reversible((a, b, c, d),(y0', y1', y2', y3'))") simp
  
    ultimately have "y_of((a, b, c, d), snd(y_inv_reversible((a, b, c, d),(y0', y1', y2', y3')))) =
                   (y0', y1', y2', y3')"
      using `snd(y_reversible(y_inv_reversible((a, b, c, d),(y0', y1', y2', y3')))) = (y0', y1', y2', y3')`
      by simp
  
    then show ?thesis
      using x_tuple by simp
  qed

  have "x0^2 + x1^2 + x2^2 + x3^2 = 
      (y0'^2 + y1'^2 + y2'^2 + y3'^2) / of_nat(a^2 + b^2 + c^2 + d^2)"
  proof -
    have "one_of(y_of((a, b, c, d),(x0, x1, x2, x3)))^2 +
        two_of(y_of((a, b, c, d),(x0, x1, x2, x3)))^2 +
        three_of(y_of((a, b, c, d),(x0, x1, x2, x3)))^2 +
        four_of(y_of((a, b, c, d),(x0, x1, x2, x3)))^2 = 
        of_nat (a^2 + b^2 + c^2 + d^2) * (x0^2 + x1^2 + x2^2 + x3^2)"
      using lagrange_trans_of_4_identity by simp
  
    then have "(y0'^2 + y1'^2 + y2'^2 + y3'^2) = 
             of_nat (a^2 + b^2 + c^2 + d^2) * (x0^2 + x1^2 + x2^2 + x3^2)"
      using `y_of((a, b, c, d),(x0, x1, x2, x3)) = (y0', y1', y2', y3')` by simp
  
    moreover have "a^2 + b^2 + c^2 + d^2 ≠ 0"
      using four_sq blocksize_gt_index by simp
  
    then have "of_nat (a^2 + b^2 + c^2 + d^2) ≠ (0::rat)"
      by linarith

    ultimately show ?thesis by (simp add: field_simps)
  qed

  then have x_in_terms_of_y: "x $$ (m-4, 0)^2 + x $$ (m-3, 0)^2 + 
                              x $$ (m-2, 0)^2 + x $$ (m-1, 0)^2 =
                              (y0'^2 + y1'^2 + y2'^2 + y3'^2) / of_nat(𝗄 - Λ)"
    using four_sq x_at_m4 x_at_m3 x_at_m2 x_at_m1 by simp

  have eq_for_y0: "(∑h ∈ {0..<m}. of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) = 
                 e00 * y0 + e10 * y1' + e20 * y2' + e30 * y3' +
                 (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0))"
  sorry (* This needs to be derived from Li0 and the y-definitions *)

  have eq_for_y1: "(∑h ∈ {0..<m}. of_int(N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) = 
                 e01 * y0' + e11 * y1 + e21 * y2' + e31 * y3' +
                 (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-3)) * x $$ (m-h-1,0))"
  sorry

  have eq_for_y2: "(∑h ∈ {0..<m}. of_int(N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) = 
                 e02 * y0' + e12 * y1' + e22 * y2 + e32 * y3' +
                 (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-2)) * x $$ (m-h-1,0))"
  sorry

  have eq_for_y3: "(∑h ∈ {0..<m}. of_int(N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) = 
                 e03 * y0' + e13 * y1' + e23 * y2' + e33 * y3 +
                 (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-1)) * x $$ (m-h-1,0))"
  sorry

(* Now apply induction_step lemmas *)
  have a_form: "of_nat(a^2 + b^2 + c^2 + d^2) = of_int(𝗄 - Λ)"
    using four_sq by simp

  have y0_squared: "y0^2 = L0^2"
    using induction_step_0[OF a_form m_props(2) m_props(1) eq_for_y0 y0_def]
    unfolding L0_def by simp

  have y1_squared: "y1^2 = L1^2"
    using induction_step_1[OF a_form m_props(2) m_props(1) eq_for_y1 y1_def]
    unfolding L1_def by simp

  have y2_squared: "y2^2 = L2^2"
    using induction_step_2[OF a_form m_props(2) m_props(1) eq_for_y2 y2_def]
    unfolding L2_def by simp

  have y3_squared: "y3^2 = L3^2"
    using induction_step_3[OF a_form m_props(2) m_props(1) eq_for_y3 y3_def]
    unfolding L3_def by simp

(* Therefore *)
  have sum_y_squared: "y0^2 + y1^2 + y2^2 + y3^2 = L0^2 + L1^2 + L2^2 + L3^2"
    using y0_squared y1_squared y2_squared y3_squared by simp

(* Now connect everything via brc_x_equation *)

(* Most x entries are 0, only the 4 at m-4, m-3, m-2, m-1 are nonzero *)
  have x_mostly_zero: "∀j < m. j ∉ {m-4, m-3, m-2, m-1} ⟶ x $$ (j, 0) = 0"
    using x_def m_props by auto

(* So ∑x only has 4 terms (for j < m; for j ≥ m, x doesn't have those rows) *)
  have sum_x_simple: "(∑j ∈ {0..<𝗏}. x $$ (j, 0)) = x0 + x1 + x2 + x3"
  proof -
    have "(∑j ∈ {0..<𝗏}. x $$ (j, 0)) = (∑j ∈ {0..<m}. x $$ (j, 0)) + (∑j ∈ {m..<𝗏}. x $$ (j, 0))"
    sorry
    moreover have "(∑j ∈ {m..<𝗏}. x $$ (j, 0)) = 0"
    sorry (* x is only m rows, so indices ≥ m give 0 or undefined *)
    moreover have "(∑j ∈ {0..<m}. x $$ (j, 0)) = x0 + x1 + x2 + x3"
      using x_mostly_zero x_at_m4 x_at_m3 x_at_m2 x_at_m1 sorry
    ultimately show ?thesis by simp
  qed

(* Similarly ∑x² only has 4 terms *)
  have sum_x_sq_simple: "(∑j ∈ {0..<𝗏}. (x $$ (j, 0))^2) = x0^2 + x1^2 + x2^2 + x3^2"
    using x_split first_four x_at_m4 x_at_m3 x_at_m2 x_at_m1 sorry

(* Substitute into brc *)
  have brc_simplified: "(∑i ∈ {0..<𝗏}. (∑h ∈ {0..<𝗏}. of_int(N $$ (h,i)) * x $$ (h,0))^2) =
                      of_int Λ * (x0 + x1 + x2 + x3)^2 + 
                      of_int(𝗄 - Λ) * (x0^2 + x1^2 + x2^2 + x3^2)"
    using brc sum_x_simple sum_x_sq_simple by simp

(* Use x in terms of y' *)
  have "(x0^2 + x1^2 + x2^2 + x3^2) = (y0'^2 + y1'^2 + y2'^2 + y3'^2) / of_nat(𝗄 - Λ)"
    using `x0^2 + x1^2 + x2^2 + x3^2 = (y0'^2 + y1'^2 + y2'^2 + y3'^2) / of_nat(a^2 + b^2 + c^2 + d^2)`
        four_sq by simp

  then have brc_with_y': "(∑i ∈ {0..<𝗏}. (∑h ∈ {0..<𝗏}. of_int(N $$ (h,i)) * x $$ (h,0))^2) =
                        of_int Λ * (x0 + x1 + x2 + x3)^2 + 
                        (y0'^2 + y1'^2 + y2'^2 + y3'^2)"
  proof -
    have kl_pos: "𝗄 - Λ > 0" using blocksize_gt_index by simp
    then have kl_nz: "of_nat(𝗄 - Λ) ≠ (0::rat)" by simp
  
    have "of_nat(𝗄 - Λ) * (x0^2 + x1^2 + x2^2 + x3^2) = (y0'^2 + y1'^2 + y2'^2 + y3'^2)"
      using `(x0^2 + x1^2 + x2^2 + x3^2) = (y0'^2 + y1'^2 + y2'^2 + y3'^2) / of_nat(𝗄 - Λ)`
        kl_nz by (simp add: field_simps)
  
    then show ?thesis
      using brc_simplified by (simp add: field_simps)
  qed

(* The LHS equals L0² + L1² + L2² + L3² plus remaining terms *)
(* But we know L0² + L1² + L2² + L3² = y0² + y1² + y2² + y3² *)

(* The key: for some specific choice of y0', y1', y2', y3', the remaining terms vanish or simplify *)
(* This gives us a Pell equation *)

(* For now, show existence of rational solution *)
  have "∃s t :: rat. s^2 = of_int Λ * t^2 + of_int(𝗄 - Λ) ∧ (s ≠ 0 ∨ t ≠ 0)"
  proof -
  (* Choose specific y' values and use the relation *)
  (* This is the key algebraic step *)
  sorry
  qed

  then obtain s t :: rat where st: "s^2 = of_int Λ * t^2 + of_int(𝗄 - Λ)" 
    and nontrivial: "s ≠ 0 ∨ t ≠ 0"
    by blast

(* Convert to integers by clearing denominators *)
  obtain num_s denom_s num_t denom_t :: int where
    s_def: "s = of_int num_s / of_int denom_s" and
    t_def: "t = of_int num_t / of_int denom_t" and
    denom_pos: "denom_s > 0" "denom_t > 0"
  sorry (* quotient_of properties *)

  define x_int where "x_int = num_s * denom_t"
  define z_int where "z_int = denom_s * denom_t"  
  define y_int where "y_int = num_t * denom_s"

  have "of_int(x_int^2) = of_int(𝗄-Λ) * of_int(y_int^2) + of_int Λ * of_int(z_int^2)"
  sorry (* Clearing denominators from st *)

  moreover have "x_int ≠ 0 ∨ y_int ≠ 0 ∨ z_int ≠ 0"
    using nontrivial sorry

  ultimately show ?thesis by blast
qed*)
end
end
