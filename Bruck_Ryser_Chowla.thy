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

definition t_of :: "rat mat ⇒ rat" where
  "t_of x = (∑j∈{0..<𝗏}. x $$ (j,0))"

lemma brc_v_eq_4w_plus_1:
  assumes "𝗏 mod 4 = 1"
  shows "∃w. 𝗏 = 4 * w + 1"
proof
  show "𝗏 = 4 * (𝗏 div 4) + 1"
    using assms
    by (metis div_mult_mod_eq mult.commute)
qed


lemma y_norm_identity:
  fixes a b c d :: nat
  fixes x0 x1 x2 x3 :: rat
  assumes n_def: "n = a^2 + b^2 + c^2 + d^2"
  shows
    "(one_of (y_of ((a,b,c,d),(x0,x1,x2,x3))))^2 +
     (two_of (y_of ((a,b,c,d),(x0,x1,x2,x3))))^2 +
     (three_of (y_of ((a,b,c,d),(x0,x1,x2,x3))))^2 +
     (four_of (y_of ((a,b,c,d),(x0,x1,x2,x3))))^2
     =
     of_nat n * (x0^2 + x1^2 + x2^2 + x3^2)"
  unfolding n_def
  by (simp add: algebra_simps power2_eq_square)

lemma y_norm_identity_k_lambda:
  fixes a b c d :: nat
  fixes x0 x1 x2 x3 :: rat
  assumes abcd: "𝗄 - Λ = a^2 + b^2 + c^2 + d^2"
  shows
    "(one_of (y_of ((a,b,c,d),(x0,x1,x2,x3))))^2 +
     (two_of (y_of ((a,b,c,d),(x0,x1,x2,x3))))^2 +
     (three_of (y_of ((a,b,c,d),(x0,x1,x2,x3))))^2 +
     (four_of (y_of ((a,b,c,d),(x0,x1,x2,x3))))^2
     =
     of_nat (𝗄 - Λ) * (x0^2 + x1^2 + x2^2 + x3^2)"
  using y_norm_identity[of "𝗄 - Λ" a b c d x0 x1 x2 x3] abcd
  by simp

lemma y_block_sum_identity:
  fixes a b c d :: nat
  fixes x0 x1 x2 x3 :: rat
  assumes abcd: "𝗄 - Λ = a^2 + b^2 + c^2 + d^2"
  shows
    "of_nat (𝗄 - Λ) * (x0^2 + x1^2 + x2^2 + x3^2)
     =
     (one_of (y_of ((a,b,c,d),(x0,x1,x2,x3))))^2 +
     (two_of (y_of ((a,b,c,d),(x0,x1,x2,x3))))^2 +
     (three_of (y_of ((a,b,c,d),(x0,x1,x2,x3))))^2 +
     (four_of (y_of ((a,b,c,d),(x0,x1,x2,x3))))^2"
  using y_norm_identity_k_lambda[OF abcd, of x0 x1 x2 x3]
  by simp

lemma y_block_h_identity:
  fixes a b c d :: nat
  fixes x :: "rat mat"
  assumes abcd: "𝗄 - Λ = a^2 + b^2 + c^2 + d^2"
  shows
    "of_nat (𝗄 - Λ) *
      ((x $$ (4*h,0))^2 +
       (x $$ (4*h + 1,0))^2 +
       (x $$ (4*h + 2,0))^2 +
       (x $$ (4*h + 3,0))^2)
     =
     (one_of (y_of ((a,b,c,d),
        (x $$ (4*h,0), x $$ (4*h + 1,0), x $$ (4*h + 2,0), x $$ (4*h + 3,0)))))^2 +
     (two_of (y_of ((a,b,c,d),
        (x $$ (4*h,0), x $$ (4*h + 1,0), x $$ (4*h + 2,0), x $$ (4*h + 3,0)))))^2 +
     (three_of (y_of ((a,b,c,d),
        (x $$ (4*h,0), x $$ (4*h + 1,0), x $$ (4*h + 2,0), x $$ (4*h + 3,0)))))^2 +
     (four_of (y_of ((a,b,c,d),
        (x $$ (4*h,0), x $$ (4*h + 1,0), x $$ (4*h + 2,0), x $$ (4*h + 3,0)))))^2"
  using y_block_sum_identity[OF abcd,
      of "x $$ (4*h,0)"
         "x $$ (4*h + 1,0)"
         "x $$ (4*h + 2,0)"
         "x $$ (4*h + 3,0)"]
  by simp

definition y_block :: "nat ⇒ nat ⇒ nat ⇒ nat ⇒ rat mat ⇒ nat ⇒ rat" where
  "y_block a b c d x i =
    (let h = i div 4;
         r = i mod 4;
         y = y_of ((a,b,c,d),
              (x $$ (4*h,0),
               x $$ (4*h + 1,0),
               x $$ (4*h + 2,0),
               x $$ (4*h + 3,0)))
     in if r = 0 then one_of y
        else if r = 1 then two_of y
        else if r = 2 then three_of y
        else four_of y)"

definition x_block_sqsum :: "rat mat ⇒ nat ⇒ rat" where
  "x_block_sqsum x h =
     (x $$ (4*h,0))^2 +
     (x $$ (4*h + 1,0))^2 +
     (x $$ (4*h + 2,0))^2 +
     (x $$ (4*h + 3,0))^2"

definition y_block_sqsum :: "nat ⇒ nat ⇒ nat ⇒ nat ⇒ rat mat ⇒ nat ⇒ rat" where
  "y_block_sqsum a b c d x h =
     (one_of (y_of ((a,b,c,d),
        (x $$ (4*h,0), x $$ (4*h + 1,0),
         x $$ (4*h + 2,0), x $$ (4*h + 3,0)))))^2 +
     (two_of (y_of ((a,b,c,d),
        (x $$ (4*h,0), x $$ (4*h + 1,0),
         x $$ (4*h + 2,0), x $$ (4*h + 3,0)))))^2 +
     (three_of (y_of ((a,b,c,d),
        (x $$ (4*h,0), x $$ (4*h + 1,0),
         x $$ (4*h + 2,0), x $$ (4*h + 3,0)))))^2 +
     (four_of (y_of ((a,b,c,d),
        (x $$ (4*h,0), x $$ (4*h + 1,0),
         x $$ (4*h + 2,0), x $$ (4*h + 3,0)))))^2"

lemma y_block_sqsum_identity:
  fixes a b c d :: nat
  fixes x :: "rat mat"
  assumes abcd: "𝗄 - Λ = a^2 + b^2 + c^2 + d^2"
  shows "of_nat (𝗄 - Λ) * x_block_sqsum x h =
         y_block_sqsum a b c d x h"
  unfolding x_block_sqsum_def y_block_sqsum_def
  using y_block_h_identity[OF abcd, of x h]
  by simp

lemma y_blocks_sqsum_identity:
  fixes a b c d :: nat
  fixes x :: "rat mat"
  assumes abcd: "𝗄 - Λ = a^2 + b^2 + c^2 + d^2"
  shows
    "of_nat (𝗄 - Λ) * (∑h∈{0..<w}. x_block_sqsum x h)
     =
     (∑h∈{0..<w}. y_block_sqsum a b c d x h)"
proof -
  have "⋀h. h ∈ {0..<w} ⟹
    of_nat (𝗄 - Λ) * x_block_sqsum x h =
    y_block_sqsum a b c d x h"
    using y_block_sqsum_identity[OF abcd] by simp
  then have
    "(∑h∈{0..<w}. of_nat (𝗄 - Λ) * x_block_sqsum x h)
     =
     (∑h∈{0..<w}. y_block_sqsum a b c d x h)"
    by simp
  then show ?thesis
    by (simp add: sum_distrib_left)
qed

lemma brc_x_sum_split_4w_last:
  fixes x :: "rat mat"
  assumes v_form: "𝗏 = 4 * w + 1"
  shows
    "(∑j∈{0..<𝗏}. (x $$ (j,0))^2)
     =
     (∑j∈{0..<4*w}. (x $$ (j,0))^2) + (x $$ (4*w,0))^2"
proof -
  have "𝗏 = Suc (4*w)"
    using v_form by simp
  then show ?thesis
    by (simp add: sum.atLeast0_lessThan_Suc)
qed

lemma brc_x_sum_split_4w_last_plain:
  fixes x :: "rat mat"
  assumes v_form: "𝗏 = 4 * w + 1"
  shows
    "(∑j∈{0..<𝗏}. x $$ (j,0))
     =
     (∑j∈{0..<4*w}. x $$ (j,0)) + x $$ (4*w,0)"
proof -
  have "𝗏 = Suc (4*w)"
    using v_form by simp
  then show ?thesis
    by (simp add: sum.atLeast0_lessThan_Suc)
qed

lemma brc_x_equation_split:
  fixes x :: "rat mat"
  assumes v_form: "𝗏 = 4 * w + 1"
  shows
   "(∑i∈{0..<𝗏}.
      (∑h∈{0..<𝗏}. of_int (N $$ (h,i)) * x $$ (h,0))^2)
    =
    of_nat Λ *
      ((∑j∈{0..<4*w}. x $$ (j,0))
        + x $$ (4*w,0))^2
    +
    of_nat (𝗄 - Λ) *
      ((∑j∈{0..<4*w}. (x $$ (j,0))^2)
        + (x $$ (4*w,0))^2)"
proof -
  have eq:
    "(∑i∈{0..<𝗏}.
    (∑h∈{0..<𝗏}. of_int (N $$ (h,i)) * x $$ (h,0))^2)
    =
    of_nat Λ * (∑j∈{0..<𝗏}. x $$ (j,0))^2
    +
    of_nat (𝗄 - Λ) * (∑j∈{0..<𝗏}. (x $$ (j,0))^2)"
    using brc_x_equation[of x]
    by simp

  have sq:
    "(∑j∈{0..<𝗏}. (x $$ (j,0))^2)
     =
     (∑j∈{0..<4*w}. (x $$ (j,0))^2)
      + (x $$ (4*w,0))^2"
    using brc_x_sum_split_4w_last[OF v_form] .

  have lin:
    "(∑j∈{0..<𝗏}. x $$ (j,0))
     =
     (∑j∈{0..<4*w}. x $$ (j,0))
      + x $$ (4*w,0)"
    using brc_x_sum_split_4w_last_plain[OF v_form] .

  show ?thesis
    using eq sq lin
    by simp
qed

definition x_head_sum :: "rat mat ⇒ nat ⇒ rat" where
  "x_head_sum x w = (∑j∈{0..<4*w}. x $$ (j,0))"

definition x_head_sqsum :: "rat mat ⇒ nat ⇒ rat" where
  "x_head_sqsum x w = (∑j∈{0..<4*w}. (x $$ (j,0))^2)"

definition x_last :: "rat mat ⇒ nat ⇒ rat" where
  "x_last x w = x $$ (4*w,0)"

lemma brc_x_equation_split_named:
  fixes x :: "rat mat"
  assumes v_form: "𝗏 = 4 * w + 1"
  shows
   "(∑i∈{0..<𝗏}.
      (∑h∈{0..<𝗏}. of_int (N $$ (h,i)) * x $$ (h,0))^2)
    =
    of_nat Λ * (x_head_sum x w + x_last x w)^2
    +
    of_nat (𝗄 - Λ) *
      (x_head_sqsum x w + (x_last x w)^2)"
  using brc_x_equation_split[OF v_form, of x]
  unfolding x_head_sum_def x_head_sqsum_def x_last_def
  by simp

definition y_blocks_sqsum :: "nat ⇒ nat ⇒ nat ⇒ nat ⇒ rat mat ⇒ nat ⇒ rat" where
  "y_blocks_sqsum a b c d x w =
     (∑h∈{0..<w}. y_block_sqsum a b c d x h)"

lemma y_blocks_sqsum_identity_named:
  fixes a b c d :: nat
  fixes x :: "rat mat"
  assumes abcd: "𝗄 - Λ = a^2 + b^2 + c^2 + d^2"
  shows
    "of_nat (𝗄 - Λ) * (∑h∈{0..<w}. x_block_sqsum x h)
     =
     y_blocks_sqsum a b c d x w"
  using y_blocks_sqsum_identity[OF abcd, of x w]
  unfolding y_blocks_sqsum_def
  by simp

lemma brc_x_equation_transformed_conditional:
  fixes a b c d :: nat
  fixes x :: "rat mat"
  assumes v_form: "𝗏 = 4 * w + 1"
  assumes abcd: "𝗄 - Λ = a^2 + b^2 + c^2 + d^2"
  assumes head_blocks:
    "x_head_sqsum x w = (∑h∈{0..<w}. x_block_sqsum x h)"
  shows
   "(∑i∈{0..<𝗏}.
      (∑h∈{0..<𝗏}. of_int (N $$ (h,i)) * x $$ (h,0))^2)
    =
    of_nat Λ * (x_head_sum x w + x_last x w)^2
    +
    y_blocks_sqsum a b c d x w
    +
    of_nat (𝗄 - Λ) * (x_last x w)^2"
proof -
  have split_eq:
   "(∑i∈{0..<𝗏}.
      (∑h∈{0..<𝗏}. of_int (N $$ (h,i)) * x $$ (h,0))^2)
    =
    of_nat Λ * (x_head_sum x w + x_last x w)^2
    +
    of_nat (𝗄 - Λ) *
      (x_head_sqsum x w + (x_last x w)^2)"
    using brc_x_equation_split_named[OF v_form, of x] .

  have block_eq:
    "of_nat (𝗄 - Λ) * x_head_sqsum x w =
     y_blocks_sqsum a b c d x w"
  proof -
    have "of_nat (𝗄 - Λ) * x_head_sqsum x w =
          of_nat (𝗄 - Λ) * (∑h∈{0..<w}. x_block_sqsum x h)"
      using head_blocks by simp
    also have "... = y_blocks_sqsum a b c d x w"
      using y_blocks_sqsum_identity_named[OF abcd, of x w] .
    finally show ?thesis .
  qed

  show ?thesis
    using split_eq block_eq
    by (simp add: algebra_simps)
qed

lemma sum_first_4_Suc_split:
  fixes f :: "nat ⇒ rat"
  shows "(∑j = 0..<4 + n * 4. f j)
       =
       f (n * 4) + f (Suc (n * 4)) +
       f (Suc (Suc (n * 4))) + f (3 + n * 4) +
       (∑j = 0..<n * 4. f j)"
proof -
  have "(∑j = 0..<4 + n * 4. f j)
      = (∑j = 0..<n * 4. f j) + (∑j = n * 4..<4 + n * 4. f j)"
    by (simp add: sum.atLeastLessThan_concat)
  also have "(∑j = n * 4..<4 + n * 4. f j)
      = f (n * 4) + f (Suc (n * 4)) + f (Suc (Suc (n * 4))) + f (3 + n * 4)"
    by (simp add: numeral_eq_Suc)
  finally show ?thesis
    by (simp add: algebra_simps)
qed

lemma sum_x_first_4w_as_blocks:
  fixes x :: "rat mat"
  shows "x_head_sqsum x w = (∑h∈{0..<w}. x_block_sqsum x h)"
proof (induct w)
  case 0
  show ?case
    unfolding x_head_sqsum_def x_block_sqsum_def
    by simp
next
  case (Suc n)
  have IH:
    "x_head_sqsum x n = (∑h∈{0..<n}. x_block_sqsum x h)"
    using Suc.hyps by simp

  have split:
    "x_head_sqsum x (Suc n)
     =
     x_head_sqsum x n + x_block_sqsum x n"
    unfolding x_head_sqsum_def x_block_sqsum_def
    using sum_first_4_Suc_split[of "λj. (x $$ (j,0))^2" n]
    by (simp add: algebra_simps)

  show ?case
    using IH split
    by simp
qed

lemma brc_x_equation_transformed:
  fixes a b c d :: nat
  fixes x :: "rat mat"
  assumes v_form: "𝗏 = 4 * w + 1"
  assumes abcd: "𝗄 - Λ = a^2 + b^2 + c^2 + d^2"
  shows
   "(∑i∈{0..<𝗏}.
      (∑h∈{0..<𝗏}. of_int (N $$ (h,i)) * x $$ (h,0))^2)
    =
    of_nat Λ * (x_head_sum x w + x_last x w)^2
    +
    y_blocks_sqsum a b c d x w
    +
    of_nat (𝗄 - Λ) * (x_last x w)^2"
  using brc_x_equation_transformed_conditional[
    OF v_form abcd sum_x_first_4w_as_blocks]
  by simp

definition brc_y0 :: "rat mat ⇒ nat ⇒ rat" where
  "brc_y0 x w = x_head_sum x w + x_last x w"

definition brc_yv :: "rat mat ⇒ nat ⇒ rat" where
  "brc_yv x w = x_last x w"

definition brc_L :: "rat mat ⇒ nat ⇒ rat" where
  "brc_L x i =
     (∑h∈{0..<𝗏}. of_int (N $$ (h,i)) * x $$ (h,0))"

lemma brc_x_equation_transformed_named:
  fixes a b c d :: nat
  fixes x :: "rat mat"
  assumes v_form: "𝗏 = 4 * w + 1"
  assumes abcd: "𝗄 - Λ = a^2 + b^2 + c^2 + d^2"
  shows
   "(∑i∈{0..<𝗏}. (brc_L x i)^2)
    =
    of_nat Λ * (brc_y0 x w)^2
    +
    y_blocks_sqsum a b c d x w
    +
    of_nat (𝗄 - Λ) * (brc_yv x w)^2"
  using brc_x_equation_transformed[OF v_form abcd, of x]
  unfolding brc_L_def brc_y0_def brc_yv_def
  by simp

lemma brc_x_equation_extended:
  fixes x :: "rat mat"
  fixes xv1 :: rat
  shows
    "(∑i ∈ {0..<𝗏}.
       (∑h ∈ {0..<𝗏}.
          of_int (N $$ (h,i)) * x $$ (h,0))^2)
       + of_int (int (𝗄 - Λ)) * xv1^2
     =
       of_int (int Λ) *
         (∑j ∈ {0..<𝗏}. x $$ (j,0))^2
       + of_int (int (𝗄 - Λ)) *
         ((∑j ∈ {0..<𝗏}. (x $$ (j,0))^2) + xv1^2)"
proof -
  have base:
    "(∑i ∈ {0..<𝗏}.
       (∑h ∈ {0..<𝗏}.
          of_int (N $$ (h,i)) * x $$ (h,0))^2)
     =
       of_int (int Λ) *
         (∑j ∈ {0..<𝗏}. x $$ (j,0))^2
       + of_int (int (𝗄 - Λ)) *
         (∑j ∈ {0..<𝗏}. (x $$ (j,0))^2)"
    using brc_x_equation[of x] .

  show ?thesis
    using base
    by (simp add: algebra_simps)
qed

definition brc_extend_x :: "rat mat ⇒ rat ⇒ rat mat" where
  "brc_extend_x x xv1 =
     mat (𝗏 + 1) 1
       (λ(i,j). if i < 𝗏 then x $$ (i,0) else xv1)"

lemma brc_extend_x_old:
  assumes "i < 𝗏"
  shows "brc_extend_x x xv1 $$ (i,0) = x $$ (i,0)"
  using assms
  unfolding brc_extend_x_def
  by simp

lemma brc_extend_x_last:
  shows "brc_extend_x x xv1 $$ (𝗏,0) = xv1"
  unfolding brc_extend_x_def
  by simp

lemma brc_extend_x_sqsum:
  "(∑i∈{0..<𝗏 + 1}.
      (brc_extend_x x xv1 $$ (i,0))^2)
   =
   (∑i∈{0..<𝗏}. (x $$ (i,0))^2) + xv1^2"
proof -
  have split:
    "{0..<𝗏 + 1} = {0..<𝗏} ∪ {𝗏}"
    by auto

  have disj:
    "{0..<𝗏} ∩ {𝗏} = {}"
    by auto

  have
    "(∑i∈{0..<𝗏 + 1}.
        (brc_extend_x x xv1 $$ (i,0))^2)
     =
     (∑i∈{0..<𝗏}.
        (brc_extend_x x xv1 $$ (i,0))^2)
       + (brc_extend_x x xv1 $$ (𝗏,0))^2"
    using split disj
    by (simp add: sum.union_disjoint)

  also have
    "... =
     (∑i∈{0..<𝗏}. (x $$ (i,0))^2) + xv1^2"
    using brc_extend_x_old brc_extend_x_last
    by (intro arg_cong2[where f="(+)"]) auto

  finally show ?thesis .
qed

lemma brc_v_plus_one_four_blocks:
  assumes v_form: "𝗏 = 4 * w - 1"
  assumes w_pos: "0 < w"
  shows "𝗏 + 1 = 4 * w"
  using v_form w_pos
  by simp

lemma sum_four_blocks:
  fixes f :: "nat ⇒ rat"
  shows
    "(∑i∈{0..<4*w}. f i)
     =
     (∑h∈{0..<w}.
       (f (4*h) + f (4*h+1) + f (4*h+2) + f (4*h+3)))"
proof (induction w)
  case 0
  then show ?case
    by simp
next
  case (Suc w)

  have split:
    "{0..<4 * Suc w} =
     {0..<4*w} ∪ {4*w, 4*w+1, 4*w+2, 4*w+3}"
    by auto

  have disj:
    "{0..<4*w} ∩ {4*w, 4*w+1, 4*w+2, 4*w+3} = {}"
    by auto

  show ?case
    unfolding split
    using disj Suc.IH
    by (simp add: sum.union_disjoint algebra_simps)
qed

lemma brc_x_equation_extended_vector:
  fixes x :: "rat mat"
  fixes xv1 :: rat
  shows
    "(∑i ∈ {0..<𝗏}.
       (∑h ∈ {0..<𝗏}.
          of_int (N $$ (h,i)) * x $$ (h,0))^2)
       + of_int (int (𝗄 - Λ)) * xv1^2
     =
       of_int (int Λ) *
         (∑j ∈ {0..<𝗏}. x $$ (j,0))^2
       + of_int (int (𝗄 - Λ)) *
         (∑j ∈ {0..<𝗏 + 1}.
            (brc_extend_x x xv1 $$ (j,0))^2)"
proof -
  have ext:
    "(∑j ∈ {0..<𝗏 + 1}.
       (brc_extend_x x xv1 $$ (j,0))^2)
     =
     (∑j ∈ {0..<𝗏}. (x $$ (j,0))^2) + xv1^2"
    using brc_extend_x_sqsum[of x xv1] .

  have base:
    "(∑i ∈ {0..<𝗏}.
       (∑h ∈ {0..<𝗏}.
          of_int (N $$ (h,i)) * x $$ (h,0))^2)
       + of_int (int (𝗄 - Λ)) * xv1^2
     =
       of_int (int Λ) *
         (∑j ∈ {0..<𝗏}. x $$ (j,0))^2
       + of_int (int (𝗄 - Λ)) *
         ((∑j ∈ {0..<𝗏}. (x $$ (j,0))^2) + xv1^2)"
    using brc_x_equation_extended[of x xv1] .

  show ?thesis
    using base ext
    by simp
qed

lemma brc_extend_x_sqsum_blocks:
  assumes v_form: "𝗏 = 4 * w - 1"
  assumes w_pos: "0 < w"
  shows
    "(∑i∈{0..<𝗏 + 1}.
       (brc_extend_x x xv1 $$ (i,0))^2)
     =
     (∑h∈{0..<w}.
       ((brc_extend_x x xv1 $$ (4*h,0))^2 +
        (brc_extend_x x xv1 $$ (4*h+1,0))^2 +
        (brc_extend_x x xv1 $$ (4*h+2,0))^2 +
        (brc_extend_x x xv1 $$ (4*h+3,0))^2))"
proof -
  have size:
    "𝗏 + 1 = 4 * w"
    using brc_v_plus_one_four_blocks[OF v_form w_pos] .

  have blocks:
    "(∑i∈{0..<4*w}.
       (brc_extend_x x xv1 $$ (i,0))^2)
     =
     (∑h∈{0..<w}.
       ((brc_extend_x x xv1 $$ (4*h,0))^2 +
        (brc_extend_x x xv1 $$ (4*h+1,0))^2 +
        (brc_extend_x x xv1 $$ (4*h+2,0))^2 +
        (brc_extend_x x xv1 $$ (4*h+3,0))^2))"
    using sum_four_blocks[
      of "λi. (brc_extend_x x xv1 $$ (i,0))^2" w] .

  from blocks show ?thesis
    using size
    by simp
qed

lemma brc_extend_x_transformed_blocks:
  fixes a b c d :: nat
  fixes x :: "rat mat"
  fixes xv1 :: rat
  assumes v_form: "𝗏 = 4 * w - 1"
  assumes w_pos: "0 < w"
  assumes four_sq:
    "𝗄 - Λ = a^2 + b^2 + c^2 + d^2"
  shows
    "of_nat (𝗄 - Λ) *
       (∑i∈{0..<𝗏 + 1}.
          (brc_extend_x x xv1 $$ (i,0))^2)
     =
     (∑h∈{0..<w}.
        y_block_sqsum a b c d
          (brc_extend_x x xv1) h)"
proof -
  have blocks:
    "(∑i∈{0..<𝗏 + 1}.
       (brc_extend_x x xv1 $$ (i,0))^2)
     =
     (∑h∈{0..<w}.
        x_block_sqsum (brc_extend_x x xv1) h)"
  proof -
    have split:
      "(∑i∈{0..<𝗏 + 1}.
         (brc_extend_x x xv1 $$ (i,0))^2)
       =
       (∑h∈{0..<w}.
         ((brc_extend_x x xv1 $$ (4*h,0))^2 +
          (brc_extend_x x xv1 $$ (4*h+1,0))^2 +
          (brc_extend_x x xv1 $$ (4*h+2,0))^2 +
          (brc_extend_x x xv1 $$ (4*h+3,0))^2))"
      using brc_extend_x_sqsum_blocks[
        OF v_form w_pos, of x xv1] .

    show ?thesis
      using split
      unfolding x_block_sqsum_def
      by simp
  qed

  have block_transform:
    "⋀h. h ∈ {0..<w} ⟹
       of_nat (𝗄 - Λ) *
         x_block_sqsum (brc_extend_x x xv1) h
       =
       y_block_sqsum a b c d
         (brc_extend_x x xv1) h"
    using y_block_sqsum_identity[
      OF four_sq, of "brc_extend_x x xv1"]
    by simp

  have
    "of_nat (𝗄 - Λ) *
       (∑i∈{0..<𝗏 + 1}.
          (brc_extend_x x xv1 $$ (i,0))^2)
     =
     of_nat (𝗄 - Λ) *
       (∑h∈{0..<w}.
          x_block_sqsum (brc_extend_x x xv1) h)"
    using blocks
    by simp

  also have
    "... =
     (∑h∈{0..<w}.
        of_nat (𝗄 - Λ) *
          x_block_sqsum (brc_extend_x x xv1) h)"
    by (simp add: sum_distrib_left)

  also have
    "... =
     (∑h∈{0..<w}.
        y_block_sqsum a b c d
          (brc_extend_x x xv1) h)"
    using block_transform
    by simp

  finally show ?thesis .
qed

lemma brc_x_equation_minus_transformed:
  fixes a b c d :: nat
  fixes x :: "rat mat"
  fixes xv1 :: rat
  assumes v_form: "𝗏 = 4 * w - 1"
  assumes w_pos: "0 < w"
  assumes four_sq:
    "𝗄 - Λ = a^2 + b^2 + c^2 + d^2"
  shows
    "(∑i∈{0..<𝗏}.
       (∑h∈{0..<𝗏}.
          of_int (N $$ (h,i)) * x $$ (h,0))^2)
       + of_nat (𝗄 - Λ) * xv1^2
     =
       of_nat Λ *
         (∑j∈{0..<𝗏}. x $$ (j,0))^2
       +
       (∑h∈{0..<w}.
          y_block_sqsum a b c d
            (brc_extend_x x xv1) h)"
proof -
  have base:
    "(∑i∈{0..<𝗏}.
       (∑h∈{0..<𝗏}.
          of_int (N $$ (h,i)) * x $$ (h,0))^2)
       + of_nat (𝗄 - Λ) * xv1^2
     =
       of_nat Λ *
         (∑j∈{0..<𝗏}. x $$ (j,0))^2
       +
       of_nat (𝗄 - Λ) *
         (∑j∈{0..<𝗏 + 1}.
            (brc_extend_x x xv1 $$ (j,0))^2)"
    using brc_x_equation_extended_vector[of x xv1]
    by simp

  have transformed:
    "of_nat (𝗄 - Λ) *
       (∑j∈{0..<𝗏 + 1}.
          (brc_extend_x x xv1 $$ (j,0))^2)
     =
       (∑h∈{0..<w}.
          y_block_sqsum a b c d
            (brc_extend_x x xv1) h)"
    using brc_extend_x_transformed_blocks[
      OF v_form w_pos four_sq, of x xv1] .

  show ?thesis
    using base transformed
    by simp
qed

definition brc_match_y :: "rat ⇒ rat ⇒ rat" where
  "brc_match_y A R =
     (if A = 1 then -R / 2 else R / (1 - A))"

lemma brc_match_y_square:
  "(A * brc_match_y A R + R)^2 =
   (brc_match_y A R)^2"
proof (cases "A = 1")
  case True

  then show ?thesis
    unfolding brc_match_y_def
    by (simp add: power2_eq_square algebra_simps)
next
  case False

  have nz:
    "1 - A ≠ 0"
    using False
    by simp

  have linear:
    "A * brc_match_y A R + R =
     brc_match_y A R"
  proof -
    have
      "A * (R / (1 - A)) + R =
       (A * R + R * (1 - A)) / (1 - A)"
      using nz
      by (simp add: divide_simps)

    also have
      "... = R / (1 - A)"
      by (simp add: algebra_simps)

    finally show ?thesis
      using False
      unfolding brc_match_y_def
      by simp
  qed

  show ?thesis
    using linear
    by simp
qed

definition brc_match_coeff :: "rat ⇒ rat ⇒ rat" where
  "brc_match_coeff A B =
     (if A = 1 then -B / 2 else B / (1 - A))"

definition rat_vec_on ::
  "nat ⇒ (nat ⇒ rat) ⇒ bool" where
  "rat_vec_on n x ⟷
     (∀i. n ≤ i ⟶ x i = 0)"

definition rat_vec_zero ::
  "nat ⇒ rat" where
  "rat_vec_zero i = 0"

definition has_nontrivial_zero_on ::
  "nat ⇒ ((nat ⇒ rat) ⇒ rat) ⇒ bool" where
  "has_nontrivial_zero_on n Q ⟷
     (∃x :: nat ⇒ rat.
        rat_vec_on n x ∧
        x ≠ rat_vec_zero ∧
        Q x = 0)"

definition rat_diagonal_form ::
  "nat ⇒ (nat ⇒ rat) ⇒ (nat ⇒ rat) ⇒ rat" where
  "rat_diagonal_form n c x =
     (∑i∈{0..<n}. c i * (x i)^2)"

definition rat_scale_coordinate ::
  "nat ⇒ rat ⇒ (nat ⇒ rat) ⇒ nat ⇒ rat" where
  "rat_scale_coordinate k u x =
     (λi. if i = k then u * x i else x i)"

definition rat_linear_form ::
  "nat ⇒ (nat ⇒ rat) ⇒ (nat ⇒ rat) ⇒ rat" where
  "rat_linear_form n c y =
     (∑j∈{0..<n}. c j * y j)"

definition rat_linear_rest ::
  "nat ⇒ nat ⇒ (nat ⇒ rat) ⇒ (nat ⇒ rat) ⇒ rat" where
  "rat_linear_rest n i c y =
     (∑j∈{0..<n} - {i}. c j * y j)"

definition rat_match_substitution ::
  "nat ⇒ nat ⇒ (nat ⇒ rat) ⇒
   (nat ⇒ rat) ⇒ nat ⇒ rat" where
  "rat_match_substitution n i c y =
     (λj.
        if j = i then
          brc_match_y
            (c i)
            (rat_linear_rest n i c y)
        else
          y j)"

lemma rat_linear_form_split:
  assumes i_bound:
    "i < n"
  shows
    "rat_linear_form n c y
     =
     c i * y i +
     rat_linear_rest n i c y"
proof -
  have i_mem:
    "i ∈ {0..<n}"
    using i_bound
    by simp

  have finite:
    "finite {0..<n}"
    by simp

  have split:
    "(∑j∈{0..<n}. c j * y j)
     =
     c i * y i +
     (∑j∈{0..<n} - {i}. c j * y j)"
    using sum.remove[OF finite i_mem,
      of "λj. c j * y j"]
    by simp

  show ?thesis
    unfolding rat_linear_form_def
      rat_linear_rest_def
    using split
    by simp
qed

lemma rat_linear_rest_match_substitution:
  "rat_linear_rest n i c
      (rat_match_substitution n i c y)
   =
   rat_linear_rest n i c y"
proof -
  show ?thesis
    unfolding rat_linear_rest_def
      rat_match_substitution_def
    by (intro sum.cong) auto
qed

lemma rat_match_substitution_at:
  "rat_match_substitution n i c y i
   =
   brc_match_y
     (c i)
     (rat_linear_rest n i c y)"
  unfolding rat_match_substitution_def
  by simp

lemma rat_linear_form_match_square:
  assumes i_bound:
    "i < n"
  shows
    "(rat_linear_form n c
       (rat_match_substitution n i c y))^2
     =
     (rat_match_substitution n i c y i)^2"
proof -
  let ?R =
    "rat_linear_rest n i c y"

  let ?z =
    "rat_match_substitution n i c y"

  have rest:
    "rat_linear_rest n i c ?z = ?R"
    using rat_linear_rest_match_substitution[
      of n i c y]
    .

  have coordinate:
    "?z i = brc_match_y (c i) ?R"
    using rat_match_substitution_at[
      of n i c y]
    .

  have split:
    "rat_linear_form n c ?z
     =
     c i * ?z i +
     rat_linear_rest n i c ?z"
    using rat_linear_form_split[
      OF i_bound,
      of c ?z]
    .

  have form:
    "rat_linear_form n c ?z
     =
     c i * brc_match_y (c i) ?R + ?R"
    using split coordinate rest
    by simp

  have matched:
    "(c i * brc_match_y (c i) ?R + ?R)^2
     =
     (brc_match_y (c i) ?R)^2"
    using brc_match_y_square[
      of "c i" ?R]
    .

  show ?thesis
    using form coordinate matched
    by simp
qed

lemma rat_diagonal_form_split:
  fixes c :: "nat ⇒ rat"
  assumes i_bound:
    "i < n"
  shows
    "rat_diagonal_form n c x
     =
     c i * (x i)^2 +
     (∑j∈{0..<n} - {i}.
        c j * (x j)^2)"
proof -
  have i_mem:
    "i ∈ {0..<n}"
    using i_bound
    by simp

  have finite:
    "finite {0..<n}"
    by simp

  have split:
    "(∑j∈{0..<n}. c j * (x j)^2)
     =
     c i * (x i)^2 +
     (∑j∈{0..<n} - {i}.
        c j * (x j)^2)"
    using sum.remove[OF finite i_mem,
      of "λj. c j * (x j)^2"]
    by simp

  show ?thesis
    unfolding rat_diagonal_form_def
    using split
    by simp
qed

lemma rat_diagonal_rest_match_substitution:
  fixes d :: "nat ⇒ rat"
  shows
    "(∑j∈{0..<n} - {i}.
       d j *
       (rat_match_substitution n i c y j)^2)
     =
     (∑j∈{0..<n} - {i}.
       d j * (y j)^2)"
proof -
  show ?thesis
    apply (rule sum.cong)
     apply (rule refl)
    unfolding rat_match_substitution_def
    by auto
qed

lemma rat_match_substitution_cancels_coordinate:
  fixes c d :: "nat ⇒ rat"
  assumes i_bound:
    "i < n"
  assumes unit_coeff:
    "d i = 1"
  shows
    "rat_diagonal_form n d
       (rat_match_substitution n i c y)
     -
     (rat_linear_form n c
       (rat_match_substitution n i c y))^2
     =
     (∑j∈{0..<n} - {i}.
        d j * (y j)^2)"
proof -
  let ?z =
    "rat_match_substitution n i c y"

  have diagonal:
    "rat_diagonal_form n d ?z
     =
     d i * (?z i)^2 +
     (∑j∈{0..<n} - {i}.
        d j * (?z j)^2)"
    using rat_diagonal_form_split[
      OF i_bound, of d ?z]
    .

  have square:
    "(rat_linear_form n c ?z)^2
     =
     (?z i)^2"
    using rat_linear_form_match_square[
      OF i_bound, of c y]
    .

  have rest:
    "(∑j∈{0..<n} - {i}.
       d j * (?z j)^2)
     =
     (∑j∈{0..<n} - {i}.
       d j * (y j)^2)"
    using rat_diagonal_rest_match_substitution[
      where n = n
        and i = i
        and d = d
        and c = c
        and y = y]
    .

  show ?thesis
    using diagonal square rest unit_coeff
    by simp
qed

definition rat_zero_coordinate ::
  "nat ⇒ (nat ⇒ rat) ⇒ nat ⇒ rat" where
  "rat_zero_coordinate i y =
     (λj. if j = i then 0 else y j)"

lemma rat_zero_coordinate_at:
  "rat_zero_coordinate i y i = 0"
  unfolding rat_zero_coordinate_def
  by simp

lemma rat_zero_coordinate_other:
  assumes ji:
    "j ≠ i"
  shows
    "rat_zero_coordinate i y j = y j"
  using ji
  unfolding rat_zero_coordinate_def
  by simp

lemma rat_diagonal_form_zero_coordinate:
  fixes d :: "nat ⇒ rat"
  assumes i_bound:
    "i < n"
  shows
    "rat_diagonal_form n d
       (rat_zero_coordinate i y)
     =
     (∑j∈{0..<n} - {i}.
        d j * (y j)^2)"
proof -
  have split:
    "rat_diagonal_form n d
       (rat_zero_coordinate i y)
     =
     d i * (rat_zero_coordinate i y i)^2 +
     (∑j∈{0..<n} - {i}.
        d j *
        (rat_zero_coordinate i y j)^2)"
    using rat_diagonal_form_split[
      where n = n
        and i = i
        and c = d
        and x = "rat_zero_coordinate i y",
      OF i_bound]
    .

  have at_zero:
    "rat_zero_coordinate i y i = 0"
    using rat_zero_coordinate_at .

  have rest:
    "(∑j∈{0..<n} - {i}.
       d j * (rat_zero_coordinate i y j)^2)
     =
     (∑j∈{0..<n} - {i}.
       d j * (y j)^2)"
  proof -
    show ?thesis
      apply (rule sum.cong)
       apply (rule refl)
    using rat_zero_coordinate_other
      by auto
  qed

  show ?thesis
    using split at_zero rest
    by simp
qed

lemma brc_match_y_linear:
  "brc_match_y A (B * y)
   =
   brc_match_coeff A B * y"
  unfolding brc_match_y_def brc_match_coeff_def
  by (cases "A = 1"; simp add: algebra_simps)

lemma brc_match_y_add:
  "brc_match_y A (R + S)
   =
   brc_match_y A R + brc_match_y A S"
proof (cases "A = 1")
  case True

  show ?thesis
    unfolding brc_match_y_def
    using True
    by (simp; linarith)
next
  case False

  have nz:
    "1 - A ≠ 0"
    using False
    by simp

  show ?thesis
    unfolding brc_match_y_def
    using False nz
    by (simp add: add_divide_distrib)
qed

lemma brc_match_y_sum:
  assumes finite:
    "finite S"
  shows
    "brc_match_y A (∑j∈S. f j)
     =
     (∑j∈S. brc_match_y A (f j))"
  using finite
proof (induction S rule: finite_induct)
  case empty

  show ?case
    unfolding brc_match_y_def
    by simp
next
  case (insert j S)

  have add:
    "brc_match_y A
       (f j + (∑k∈S. f k))
     =
     brc_match_y A (f j) +
     brc_match_y A (∑k∈S. f k)"
    using brc_match_y_add[
      where A = A
        and R = "f j"
        and S = "∑k∈S. f k"]
    .

  show ?case
    using insert add
    by simp
qed

lemma rat_match_substitution_at_linear:
  "rat_match_substitution n i c y i
   =
   (∑j∈{0..<n} - {i}.
      brc_match_coeff (c i) (c j) * y j)"
proof -
  have at:
    "rat_match_substitution n i c y i
     =
     brc_match_y
       (c i)
       (rat_linear_rest n i c y)"
    using rat_match_substitution_at[
      where n = n
        and i = i
        and c = c
        and y = y]
    .

  have expanded:
    "brc_match_y
       (c i)
       (rat_linear_rest n i c y)
     =
     (∑j∈{0..<n} - {i}.
        brc_match_y
          (c i)
          (c j * y j))"
  proof -
    show ?thesis
      unfolding rat_linear_rest_def
      using brc_match_y_sum[
        where A = "c i"
          and S = "{0..<n} - {i}"
          and f = "λj. c j * y j"]
      by simp
  qed

  have linear:
    "(∑j∈{0..<n} - {i}.
       brc_match_y
         (c i)
         (c j * y j))
     =
     (∑j∈{0..<n} - {i}.
       brc_match_coeff (c i) (c j) * y j)"
  proof -
    show ?thesis
      apply (rule sum.cong)
       apply (rule refl)
      using brc_match_y_linear
      by simp
  qed

  show ?thesis
    using at expanded linear
    by simp
qed

definition rat_match_pullback_coeff ::
  "nat ⇒ nat ⇒
   (nat ⇒ rat) ⇒
   (nat ⇒ rat) ⇒
   nat ⇒ rat" where
  "rat_match_pullback_coeff n i c e =
     (λj.
        if j = i then
          0
        else
          e j +
          e i * brc_match_coeff (c i) (c j))"

lemma rat_linear_form_match_substitution:
  fixes c e :: "nat ⇒ rat"
  assumes i_bound:
    "i < n"
  shows
    "rat_linear_form n e
       (rat_match_substitution n i c y)
     =
     rat_linear_form n
       (rat_match_pullback_coeff n i c e)
       y"
proof -
  let ?z =
    "rat_match_substitution n i c y"

  let ?p =
    "rat_match_pullback_coeff n i c e"

  have split:
    "rat_linear_form n e ?z
     =
     e i * ?z i +
     rat_linear_rest n i e ?z"
    using rat_linear_form_split[
      where n = n
        and i = i
        and c = e
        and y = ?z,
      OF i_bound]
    .

  have rest:
    "rat_linear_rest n i e ?z
     =
     (∑j∈{0..<n} - {i}. e j * y j)"
  proof -
    show ?thesis
      unfolding rat_linear_rest_def
      apply (rule sum.cong)
       apply (rule refl)
      unfolding rat_match_substitution_def
      by auto
  qed

  have coordinate:
    "?z i
     =
     (∑j∈{0..<n} - {i}.
        brc_match_coeff (c i) (c j) * y j)"
    using rat_match_substitution_at_linear[
      where n = n
        and i = i
        and c = c
        and y = y]
    .

  have left:
    "rat_linear_form n e ?z
     =
     (∑j∈{0..<n} - {i}.
        (e j +
         e i * brc_match_coeff (c i) (c j)) *
        y j)"
    using split rest coordinate
    by (simp add: sum_distrib_left sum.distrib algebra_simps)

  have p_at:
    "?p i = 0"
    unfolding rat_match_pullback_coeff_def
    by simp

  have right:
    "rat_linear_form n ?p y
     =
     (∑j∈{0..<n} - {i}.
        (e j +
         e i * brc_match_coeff (c i) (c j)) *
        y j)"
  proof -
    have form_split:
      "rat_linear_form n ?p y
       =
       ?p i * y i +
       rat_linear_rest n i ?p y"
      using rat_linear_form_split[
        where n = n
          and i = i
          and c = ?p
          and y = y,
        OF i_bound]
      .

    have rest_expanded:
      "rat_linear_rest n i ?p y
       =
       (∑j∈{0..<n} - {i}.
          (e j +
           e i * brc_match_coeff (c i) (c j)) *
          y j)"
      unfolding rat_linear_rest_def
        rat_match_pullback_coeff_def
      by (intro sum.cong) auto

    show ?thesis
      using form_split rest_expanded p_at
      by simp
  qed

  show ?thesis
    using left right
    by simp
qed

definition rat_elimination_update ::
  "nat ⇒ nat ⇒
   (nat ⇒ nat ⇒ rat) ⇒
   nat ⇒ nat ⇒ rat" where
  "rat_elimination_update n q C =
     (λr.
        rat_match_pullback_coeff
          n q (C q) (C r))"

primrec rat_elimination_coeffs ::
  "nat ⇒ nat ⇒
   (nat ⇒ nat ⇒ rat) ⇒
   nat ⇒ nat ⇒ rat" where
  "rat_elimination_coeffs n 0 C = C"
| "rat_elimination_coeffs n (Suc q) C =
     rat_elimination_update
       n q
       (rat_elimination_coeffs n q C)"

lemma brc_match_coeff_zero:
  "brc_match_coeff A 0 = 0"
  unfolding brc_match_coeff_def
  by simp

lemma rat_elimination_update_preserves_zero:
  assumes r_zero:
    "C r j = 0"
  assumes pivot_zero:
    "C q j = 0"
  shows
    "rat_elimination_update n q C r j = 0"
proof (cases "j = q")
  case True

  show ?thesis
    using True
    unfolding rat_elimination_update_def
      rat_match_pullback_coeff_def
    by simp
next
  case False

  have matched_zero:
    "brc_match_coeff (C q q) (C q j) = 0"
    using pivot_zero brc_match_coeff_zero
    by simp

  show ?thesis
    using False r_zero matched_zero
    unfolding rat_elimination_update_def
      rat_match_pullback_coeff_def
    by simp
qed

lemma rat_elimination_coeffs_previous_zero:
  fixes n q r j :: nat
  fixes C :: "nat ⇒ nat ⇒ rat"
  assumes j_lt:
    "j < q"
  shows
    "rat_elimination_coeffs n q C r j = 0"
proof -
  have all_r:
    "∀r. rat_elimination_coeffs n q C r j = 0"
    using j_lt
  proof (induction q)
    case 0

    then show ?case
      by simp
  next
    case (Suc q)

    show ?case
    proof
      fix r

      show
        "rat_elimination_coeffs n (Suc q) C r j = 0"
      proof (cases "j = q")
        case True

        show ?thesis
          using True
          by (simp add:
              rat_elimination_update_def
              rat_match_pullback_coeff_def)
      next
        case False

        have j_lt_q:
          "j < q"
          using Suc.prems False
          by simp

        have previous:
          "∀s. rat_elimination_coeffs n q C s j = 0"
          using Suc.IH[OF j_lt_q] .

        have r_zero:
          "rat_elimination_coeffs n q C r j = 0"
          using previous
          by blast

        have pivot_zero:
          "rat_elimination_coeffs n q C q j = 0"
          using previous
          by blast

        have updated_zero:
          "rat_elimination_update
             n q
             (rat_elimination_coeffs n q C)
             r j
           =
           0"
          using rat_elimination_update_preserves_zero[
            where n = n
              and q = q
              and C = "rat_elimination_coeffs n q C"
              and r = r
              and j = j,
            OF r_zero pivot_zero]
          .

        show ?thesis
          using updated_zero
          by simp
      qed
    qed
  qed

  show ?thesis
    using all_r
    by blast
qed

definition rat_zero_prefix ::
  "nat ⇒ (nat ⇒ rat) ⇒ nat ⇒ rat" where
  "rat_zero_prefix q y =
     (λj. if j < q then 0 else y j)"

lemma rat_zero_prefix_below:
  assumes j_lt:
    "j < q"
  shows
    "rat_zero_prefix q y j = 0"
  using j_lt
  unfolding rat_zero_prefix_def
  by simp

lemma rat_zero_prefix_from:
  assumes q_le:
    "q ≤ j"
  shows
    "rat_zero_prefix q y j = y j"
  using q_le
  unfolding rat_zero_prefix_def
  by simp

lemma rat_linear_form_zero_prefix:
  fixes c :: "nat ⇒ rat"
  assumes coefficients_zero:
    "⋀j. j < q ⟹ c j = 0"
  shows
    "rat_linear_form n c
       (rat_zero_prefix q y)
     =
     rat_linear_form n c y"
proof -
  show ?thesis
    unfolding rat_linear_form_def
  proof (rule sum.cong)
    show "{0..<n} = {0..<n}"
      by simp
  next
    fix j
    assume j_mem:
      "j ∈ {0..<n}"

    show
      "c j * rat_zero_prefix q y j
       =
       c j * y j"
    proof (cases "j < q")
      case True

      have cj:
        "c j = 0"
        using coefficients_zero[OF True] .

      show ?thesis
        using cj
        by simp
    next
      case False

      have q_le:
        "q ≤ j"
        using False
        by simp

      have coordinate:
        "rat_zero_prefix q y j = y j"
        using rat_zero_prefix_from[OF q_le] .

      show ?thesis
        using coordinate
        by simp
    qed
  qed
qed

lemma rat_match_substitution_preserves_zero_prefix:
  assumes q_bound:
    "q < n"
  shows
    "rat_zero_prefix q
       (rat_match_substitution
          n q c (rat_zero_prefix q y))
     =
     rat_match_substitution
       n q c (rat_zero_prefix q y)"
proof
  fix j

  show
    "rat_zero_prefix q
       (rat_match_substitution
          n q c (rat_zero_prefix q y)) j
     =
     rat_match_substitution
       n q c (rat_zero_prefix q y) j"
  proof (cases "j < q")
    case True

    have jq:
      "j ≠ q"
      using True
      by simp

    have input_zero:
      "rat_zero_prefix q y j = 0"
      using rat_zero_prefix_below[OF True] .

    have substituted_zero:
      "rat_match_substitution
         n q c (rat_zero_prefix q y) j = 0"
      using jq input_zero
      unfolding rat_match_substitution_def
      by simp

    show ?thesis
      using True substituted_zero
      unfolding rat_zero_prefix_def
      by simp
  next
    case False

    have q_le:
      "q ≤ j"
      using False
      by simp

    show ?thesis
      using q_le
      unfolding rat_zero_prefix_def
      by simp
  qed
qed

lemma rat_zero_coordinate_zero_prefix_Suc:
  "rat_zero_coordinate q
     (rat_zero_prefix (Suc q) y)
   =
   rat_zero_prefix (Suc q) y"
proof
  fix j

  show
    "rat_zero_coordinate q
       (rat_zero_prefix (Suc q) y) j
     =
     rat_zero_prefix (Suc q) y j"
  proof (cases "j = q")
    case True

    have q_lt:
      "q < Suc q"
      by simp

    have prefix_zero:
      "rat_zero_prefix (Suc q) y q = 0"
      using rat_zero_prefix_below[OF q_lt] .

    show ?thesis
      using True prefix_zero
      unfolding rat_zero_coordinate_def
      by simp
  next
    case False

    show ?thesis
      using False
      unfolding rat_zero_coordinate_def
      by simp
  qed
qed

lemma rat_zero_prefix_nested:
  assumes q_le:
    "q ≤ s"
  shows
    "rat_zero_prefix q
       (rat_zero_prefix s y)
     =
     rat_zero_prefix s y"
proof
  fix j

  show
    "rat_zero_prefix q
       (rat_zero_prefix s y) j
     =
     rat_zero_prefix s y j"
  proof (cases "j < q")
    case True

    have j_lt_s:
      "j < s"
      using True q_le
      by simp

    have inner_zero:
      "rat_zero_prefix s y j = 0"
      using rat_zero_prefix_below[OF j_lt_s] .

    show ?thesis
      using True inner_zero
      unfolding rat_zero_prefix_def
      by simp
  next
    case False

    have q_le_j:
      "q ≤ j"
      using False
      by simp

    show ?thesis
      using q_le_j
      unfolding rat_zero_prefix_def
      by simp
  qed
qed

definition rat_weighted_linear_squares_from ::
  "nat ⇒ nat ⇒ nat ⇒
   (nat ⇒ rat) ⇒
   (nat ⇒ nat ⇒ rat) ⇒
   (nat ⇒ rat) ⇒ rat" where
  "rat_weighted_linear_squares_from n q m W C y =
     (∑r∈{q..<m}.
        W r * (rat_linear_form n (C r) y)^2)"

lemma rat_weighted_linear_squares_from_split:
  assumes q_lt:
    "q < m"
  shows
    "rat_weighted_linear_squares_from n q m W C y
     =
     W q * (rat_linear_form n (C q) y)^2 +
     rat_weighted_linear_squares_from
       n (Suc q) m W C y"
proof -
  have interval:
    "{q..<m} = insert q {Suc q..<m}"
    using q_lt
    by auto

  have q_not_mem:
    "q ∉ {Suc q..<m}"
    by simp

  show ?thesis
    unfolding rat_weighted_linear_squares_from_def
    using interval q_not_mem
    by simp
qed

lemma rat_weighted_linear_squares_from_match:
  assumes i_bound:
    "i < n"
  shows
    "rat_weighted_linear_squares_from n q m W C
       (rat_match_substitution n i c y)
     =
     rat_weighted_linear_squares_from n q m W
       (λr.
          rat_match_pullback_coeff
            n i c (C r))
       y"
proof -
  show ?thesis
    unfolding rat_weighted_linear_squares_from_def
  proof (rule sum.cong)
    show "{q..<m} = {q..<m}"
      by simp
  next
    fix r
    assume r_mem:
      "r ∈ {q..<m}"

    have form:
      "rat_linear_form n (C r)
         (rat_match_substitution n i c y)
       =
       rat_linear_form n
         (rat_match_pullback_coeff
           n i c (C r))
         y"
      using rat_linear_form_match_substitution[
        where n = n
          and i = i
          and c = c
          and e = "C r"
          and y = y,
        OF i_bound]
      .

    show
      "W r *
       (rat_linear_form n (C r)
          (rat_match_substitution n i c y))^2
       =
       W r *
       (rat_linear_form n
          (rat_match_pullback_coeff
            n i c (C r))
          y)^2"
      using form
      by simp
  qed
qed

lemma rat_weighted_sum_elimination_zero_prefix:
  "rat_weighted_linear_squares_from
     n q m W
     (rat_elimination_coeffs n q C)
     (rat_zero_prefix q y)
   =
   rat_weighted_linear_squares_from
     n q m W
     (rat_elimination_coeffs n q C)
     y"
proof -
  show ?thesis
    unfolding rat_weighted_linear_squares_from_def
  proof (rule sum.cong)
    show "{q..<m} = {q..<m}"
      by simp
  next
    fix r
    assume r_mem:
      "r ∈ {q..<m}"

    have form:
      "rat_linear_form n
         (rat_elimination_coeffs n q C r)
         (rat_zero_prefix q y)
       =
       rat_linear_form n
         (rat_elimination_coeffs n q C r)
         y"
    proof (rule rat_linear_form_zero_prefix)
      fix j
      assume j_lt:
        "j < q"

      show
        "rat_elimination_coeffs n q C r j = 0"
        using rat_elimination_coeffs_previous_zero[
          where n = n
            and q = q
            and C = C
            and r = r
            and j = j,
          OF j_lt]
        .
    qed

    show
      "W r *
       (rat_linear_form n
          (rat_elimination_coeffs n q C r)
          (rat_zero_prefix q y))^2
       =
       W r *
       (rat_linear_form n
          (rat_elimination_coeffs n q C r)
          y)^2"
      using form
      by simp
  qed
qed

lemma rat_weighted_elimination_stage_step:
  fixes W :: "nat ⇒ rat"
  fixes C :: "nat ⇒ nat ⇒ rat"
  fixes d :: "nat ⇒ rat"
  assumes q_lt_m:
    "q < m"
  assumes q_lt_n:
    "q < n"
  assumes weight_one:
    "W q = 1"
  assumes unit:
    "d q = 1"
  assumes stage:
    "⋀x.
       rat_weighted_linear_squares_from
         n q m W
         (rat_elimination_coeffs n q C) x
       =
       rat_diagonal_form n d
         (rat_zero_prefix q x)"
  shows
    "⋀y.
       rat_weighted_linear_squares_from
         n (Suc q) m W
         (rat_elimination_coeffs n (Suc q) C) y
       =
       rat_diagonal_form n d
         (rat_zero_prefix (Suc q) y)"
proof -
  fix y

  let ?D =
    "rat_elimination_coeffs n q C"

  let ?p =
    "?D q"

  let ?u =
    "rat_zero_prefix (Suc q) y"

  let ?z =
    "rat_match_substitution n q ?p ?u"

  have u_prefix:
    "rat_zero_prefix q ?u = ?u"
    using rat_zero_prefix_nested[
      where q = q
        and s = "Suc q"
        and y = y]
    by simp

  have z_prefix:
    "rat_zero_prefix q ?z = ?z"
  proof -
    have preserved:
      "rat_zero_prefix q
         (rat_match_substitution
            n q ?p (rat_zero_prefix q ?u))
       =
       rat_match_substitution
         n q ?p (rat_zero_prefix q ?u)"
      using rat_match_substitution_preserves_zero_prefix[
        where n = n
          and q = q
          and c = ?p
          and y = ?u,
        OF q_lt_n]
      .

    show ?thesis
      using preserved u_prefix
      by simp
  qed

  have stage_z:
    "rat_weighted_linear_squares_from
       n q m W ?D ?z
     =
     rat_diagonal_form n d ?z"
    using stage[of ?z] z_prefix
    by simp

  have split:
    "rat_weighted_linear_squares_from
       n q m W ?D ?z
     =
     (rat_linear_form n ?p ?z)^2 +
     rat_weighted_linear_squares_from
       n (Suc q) m W ?D ?z"
  proof -
    have raw:
      "rat_weighted_linear_squares_from
         n q m W ?D ?z
       =
       W q * (rat_linear_form n (?D q) ?z)^2 +
       rat_weighted_linear_squares_from
         n (Suc q) m W ?D ?z"
      using rat_weighted_linear_squares_from_split[
        where n = n
          and q = q
          and m = m
          and W = W
          and C = ?D
          and y = ?z,
        OF q_lt_m]
      .

    show ?thesis
      using raw weight_one
      by simp
  qed

  have remaining:
    "rat_weighted_linear_squares_from
       n (Suc q) m W ?D ?z
     =
     rat_diagonal_form n d ?z -
     (rat_linear_form n ?p ?z)^2"
    using stage_z split
    by linarith

  have cancellation:
    "rat_diagonal_form n d ?z -
       (rat_linear_form n ?p ?z)^2
     =
     (∑j∈{0..<n} - {q}.
        d j * (?u j)^2)"
    using rat_match_substitution_cancels_coordinate[
      where n = n
        and i = q
        and c = ?p
        and d = d
        and y = ?u,
      OF q_lt_n unit]
    .

  have diagonal_u:
    "rat_diagonal_form n d ?u
     =
     (∑j∈{0..<n} - {q}.
        d j * (?u j)^2)"
  proof -
    have zeroed:
      "rat_zero_coordinate q ?u = ?u"
      using rat_zero_coordinate_zero_prefix_Suc[
        where q = q and y = y]
      .

    have diagonal:
      "rat_diagonal_form n d
         (rat_zero_coordinate q ?u)
       =
       (∑j∈{0..<n} - {q}.
          d j * (?u j)^2)"
      using rat_diagonal_form_zero_coordinate[
        where n = n
          and i = q
          and d = d
          and y = ?u,
        OF q_lt_n]
      .

    show ?thesis
      using zeroed diagonal
      by simp
  qed

  have transformed:
    "rat_weighted_linear_squares_from
       n (Suc q) m W ?D ?z
     =
     rat_weighted_linear_squares_from
       n (Suc q) m W
       (rat_elimination_coeffs n (Suc q) C)
       ?u"
    using rat_weighted_linear_squares_from_match[
      where n = n
        and q = "Suc q"
        and m = m
        and W = W
        and i = q
        and c = ?p
        and C = ?D
        and y = ?u,
      OF q_lt_n]
    by (simp add: rat_elimination_update_def)

  have at_u:
    "rat_weighted_linear_squares_from
       n (Suc q) m W
       (rat_elimination_coeffs n (Suc q) C)
       ?u
     =
     rat_diagonal_form n d ?u"
    using remaining cancellation diagonal_u transformed
    by simp

  have remove_prefix:
    "rat_weighted_linear_squares_from
       n (Suc q) m W
       (rat_elimination_coeffs n (Suc q) C)
       ?u
     =
     rat_weighted_linear_squares_from
       n (Suc q) m W
       (rat_elimination_coeffs n (Suc q) C)
       y"
    using rat_weighted_sum_elimination_zero_prefix[
      where n = n
        and q = "Suc q"
        and m = m
        and W = W
        and C = C
        and y = y]
    .

  show
    "rat_weighted_linear_squares_from
       n (Suc q) m W
       (rat_elimination_coeffs n (Suc q) C) y
     =
     rat_diagonal_form n d
       (rat_zero_prefix (Suc q) y)"
    using at_u remove_prefix
    by simp
qed

lemma rat_weighted_elimination_iterate:
  fixes W :: "nat ⇒ rat"
  fixes C :: "nat ⇒ nat ⇒ rat"
  fixes d :: "nat ⇒ rat"
  assumes Q_le_m:
    "Q ≤ m"
  assumes Q_le_n:
    "Q ≤ n"
  assumes weights:
    "⋀q. q < Q ⟹ W q = 1"
  assumes units:
    "⋀q. q < Q ⟹ d q = 1"
  assumes initial:
    "⋀x.
       rat_weighted_linear_squares_from
         n 0 m W C x
       =
       rat_diagonal_form n d x"
  shows
    "⋀y.
       rat_weighted_linear_squares_from
         n Q m W
         (rat_elimination_coeffs n Q C) y
       =
       rat_diagonal_form n d
         (rat_zero_prefix Q y)"
  using Q_le_m Q_le_n weights units
proof (induction Q)
  case 0

  fix y

  have initial_y:
    "rat_weighted_linear_squares_from
       n 0 m W C y
     =
     rat_diagonal_form n d y"
    using initial[of y] .

  show
    "rat_weighted_linear_squares_from
       n 0 m W
       (rat_elimination_coeffs n 0 C) y
     =
     rat_diagonal_form n d
       (rat_zero_prefix 0 y)"
    using initial_y
    unfolding rat_zero_prefix_def
    by simp
next
  case (Suc Q)

  have Q_le_m:
    "Q ≤ m"
    using Suc.prems(1)
    by simp

  have Q_le_n:
    "Q ≤ n"
    using Suc.prems(2)
    by simp

  have weights_Q:
    "⋀q. q < Q ⟹ W q = 1"
    using Suc.prems(3)
    by simp

  have units_Q:
    "⋀q. q < Q ⟹ d q = 1"
    using Suc.prems(4)
    by simp

  have stage_Q:
    "⋀x.
       rat_weighted_linear_squares_from
         n Q m W
         (rat_elimination_coeffs n Q C) x
       =
       rat_diagonal_form n d
         (rat_zero_prefix Q x)"
    using Suc.IH[
      OF Q_le_m Q_le_n weights_Q units_Q]
    .

  have Q_lt_m:
    "Q < m"
    using Suc.prems(1)
    by simp

  have Q_lt_n:
    "Q < n"
    using Suc.prems(2)
    by simp

  have weight_Q:
    "W Q = 1"
    using Suc.prems(3)
    by simp

  have unit_Q:
    "d Q = 1"
    using Suc.prems(4)
    by simp

  show ?case
    using rat_weighted_elimination_stage_step[
      where n = n
        and q = Q
        and m = m
        and W = W
        and C = C
        and d = d,
      OF Q_lt_m Q_lt_n weight_Q unit_Q stage_Q]
    .
qed

lemma rat_weighted_terminal_two:
  assumes n_pos:
    "0 < n"
  shows
    "rat_weighted_linear_squares_from
       n (n - 1) (n + 1) W C y
     =
     W (n - 1) *
       (rat_linear_form n (C (n - 1)) y)^2
     +
     W n *
       (rat_linear_form n (C n) y)^2"
proof -
  obtain t where n_eq:
    "n = Suc t"
    using n_pos
    by (cases n) auto

  show ?thesis
    unfolding rat_weighted_linear_squares_from_def
    using n_eq
    by simp
qed

lemma rat_diagonal_form_zero_prefix_last:
  assumes n_pos:
    "0 < n"
  shows
    "rat_diagonal_form n d
       (rat_zero_prefix (n - 1) y)
     =
     d (n - 1) * (y (n - 1))^2"
proof -
  obtain t where n_eq:
    "n = Suc t"
    using n_pos
    by (cases n) auto

  show ?thesis
    unfolding rat_diagonal_form_def
      rat_zero_prefix_def
    using n_eq
    by simp
qed

lemma rat_weighted_elimination_terminal:
  fixes C :: "nat ⇒ nat ⇒ rat"
  fixes d W :: "nat ⇒ rat"
  fixes lam delta :: rat
  assumes n_pos:
    "0 < n"
  assumes form_weights:
    "⋀q. q < n ⟹ W q = 1"
  assumes carried_weight:
    "W n = -lam"
  assumes unit_diagonal:
    "⋀q. q < n - 1 ⟹ d q = 1"
  assumes last_diagonal:
    "d (n - 1) = delta"
  assumes initial:
    "⋀x.
       rat_weighted_linear_squares_from
         n 0 (n + 1) W C x
       =
       rat_diagonal_form n d x"
  shows
    "⋀y.
       (rat_linear_form n
          (rat_elimination_coeffs
            n (n - 1) C (n - 1))
          y)^2
       -
       lam *
       (rat_linear_form n
          (rat_elimination_coeffs
            n (n - 1) C n)
          y)^2
       =
       delta * (y (n - 1))^2"
proof -
  fix y

  have Q_le_m:
    "n - 1 ≤ n + 1"
    by simp

  have Q_le_n:
    "n - 1 ≤ n"
    by simp

  have weights:
    "⋀q. q < n - 1 ⟹ W q = 1"
    using form_weights
    by simp

  have iterated:
    "rat_weighted_linear_squares_from
       n (n - 1) (n + 1) W
       (rat_elimination_coeffs n (n - 1) C) y
     =
     rat_diagonal_form n d
       (rat_zero_prefix (n - 1) y)"
    using rat_weighted_elimination_iterate[
      where n = n
        and Q = "n - 1"
        and m = "n + 1"
        and W = W
        and C = C
        and d = d,
      OF Q_le_m Q_le_n weights
         unit_diagonal initial]
    .

  have left_expanded:
    "rat_weighted_linear_squares_from
       n (n - 1) (n + 1) W
       (rat_elimination_coeffs n (n - 1) C) y
     =
     (rat_linear_form n
        (rat_elimination_coeffs
          n (n - 1) C (n - 1))
        y)^2
     -
     lam *
     (rat_linear_form n
        (rat_elimination_coeffs
          n (n - 1) C n)
        y)^2"
  proof -
    have terminal:
      "rat_weighted_linear_squares_from
         n (n - 1) (n + 1) W
         (rat_elimination_coeffs n (n - 1) C) y
       =
       W (n - 1) *
         (rat_linear_form n
           (rat_elimination_coeffs
             n (n - 1) C (n - 1))
           y)^2
       +
       W n *
         (rat_linear_form n
           (rat_elimination_coeffs
             n (n - 1) C n)
           y)^2"
      using rat_weighted_terminal_two[
        where n = n
          and W = W
          and C = "rat_elimination_coeffs n (n - 1) C"
          and y = y,
        OF n_pos]
      .

    have last_form_weight:
      "W (n - 1) = 1"
      using form_weights n_pos
      by simp

    show ?thesis
      using terminal last_form_weight carried_weight
      by simp
  qed

  have right_expanded:
    "rat_diagonal_form n d
       (rat_zero_prefix (n - 1) y)
     =
     delta * (y (n - 1))^2"
    using rat_diagonal_form_zero_prefix_last[
      where n = n and d = d and y = y,
      OF n_pos]
      last_diagonal
    by simp

  show
    "(rat_linear_form n
       (rat_elimination_coeffs
         n (n - 1) C (n - 1))
       y)^2
     -
     lam *
       (rat_linear_form n
         (rat_elimination_coeffs
           n (n - 1) C n)
         y)^2
     =
     delta * (y (n - 1))^2"
    using iterated left_expanded right_expanded
    by simp
qed

definition rat_unit_coordinate ::
  "nat ⇒ nat ⇒ rat" where
  "rat_unit_coordinate k =
     (λj. if j = k then 1 else 0)"

lemma rat_weighted_elimination_nontrivial_solution:
  fixes C :: "nat ⇒ nat ⇒ rat"
  fixes d W :: "nat ⇒ rat"
  fixes lam delta :: rat
  assumes n_pos:
    "0 < n"
  assumes form_weights:
    "⋀q. q < n ⟹ W q = 1"
  assumes carried_weight:
    "W n = -lam"
  assumes unit_diagonal:
    "⋀q. q < n - 1 ⟹ d q = 1"
  assumes last_diagonal:
    "d (n - 1) = delta"
  assumes initial:
    "⋀x.
       rat_weighted_linear_squares_from
         n 0 (n + 1) W C x
       =
       rat_diagonal_form n d x"
  shows
    "∃x y z :: rat.
       (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧
       x^2 = delta * y^2 + lam * z^2"
proof -
  let ?u =
    "rat_unit_coordinate (n - 1)"

  let ?x =
    "rat_linear_form n
       (rat_elimination_coeffs
         n (n - 1) C (n - 1))
       ?u"

  let ?z =
    "rat_linear_form n
       (rat_elimination_coeffs
         n (n - 1) C n)
       ?u"

  have terminal:
    "?x^2 - lam * ?z^2
     =
     delta * (?u (n - 1))^2"
    using rat_weighted_elimination_terminal[
      where n = n
        and C = C
        and d = d
        and W = W
        and lam = lam
        and delta = delta,
      OF n_pos form_weights carried_weight
         unit_diagonal last_diagonal initial,
      of ?u]
    .

  have unit_value:
    "?u (n - 1) = 1"
    unfolding rat_unit_coordinate_def
    by simp

  have rearranged:
    "?x^2
     =
     delta * (?u (n - 1))^2 +
     lam * ?z^2"
  proof -
    have
      "?x^2
       =
       (?x^2 - lam * ?z^2) +
       lam * ?z^2"
      by simp

    also have
      "... =
       delta * (?u (n - 1))^2 +
       lam * ?z^2"
      using terminal
      by simp

    finally show ?thesis .
  qed

  have equation:
    "?x^2 = delta * (1::rat)^2 + lam * ?z^2"
    using rearranged unit_value
    by simp

  have nonzero:
    "?x ≠ 0 ∨ (1::rat) ≠ 0 ∨ ?z ≠ 0"
    by simp

  show ?thesis
    using equation nonzero
    by blast
qed

definition brc_tuple_component ::
  "(rat × rat × rat × rat) ⇒ nat ⇒ rat" where
  "brc_tuple_component t j =
     (if j = 0 then one_of t
      else if j = 1 then two_of t
      else if j = 2 then three_of t
      else four_of t)"

definition brc_inverse_y_block ::
  "nat ⇒ nat ⇒ nat ⇒ nat ⇒
   (nat ⇒ rat) ⇒ nat ⇒ nat ⇒ rat" where
  "brc_inverse_y_block a b c d y h j =
     brc_tuple_component
       (y_inv_of
         ((a,b,c,d),
          (y (4*h),
           y (4*h+1),
           y (4*h+2),
           y (4*h+3))))
       j"

definition brc_x_from_y_plus ::
  "nat ⇒ nat ⇒ nat ⇒ nat ⇒
   nat ⇒ (nat ⇒ rat) ⇒ rat mat" where
  "brc_x_from_y_plus a b c d w y =
     mat 𝗏 1
       (λ(i,j).
          if j ≠ 0 then 0
          else if i < 4*w then
            brc_inverse_y_block
              a b c d y (i div 4) (i mod 4)
          else
            y i)"

lemma brc_x_from_y_plus_block:
  assumes v_form:
    "𝗏 = 4 * w + 1"
  assumes h_lt:
    "h < w"
  assumes j_lt:
    "j < 4"
  shows
    "brc_x_from_y_plus a b c d w y
       $$ (4*h+j,0)
     =
     brc_inverse_y_block a b c d y h j"
proof -
  have index_lt:
    "4*h+j < 𝗏"
    using v_form h_lt j_lt
    by simp

  have before_last:
    "4*h+j < 4*w"
    using h_lt j_lt
    by simp

  have div:
    "(4*h+j) div 4 = h"
    using j_lt
    by simp

  have mod:
    "(4*h+j) mod 4 = j"
    using j_lt
    by simp

  show ?thesis
    unfolding brc_x_from_y_plus_def
    using index_lt before_last div mod
    by simp
qed

lemma brc_x_from_y_plus_last:
  assumes v_form:
    "𝗏 = 4 * w + 1"
  shows
    "brc_x_from_y_plus a b c d w y
       $$ (4*w,0)
     =
     y (4*w)"
proof -
  have index_lt:
    "4*w < 𝗏"
    using v_form
    by simp

  show ?thesis
    unfolding brc_x_from_y_plus_def
    using index_lt
    by simp
qed

lemma brc_inverse_y_block_tuple:
  "(brc_inverse_y_block a b c d y h 0,
    brc_inverse_y_block a b c d y h 1,
    brc_inverse_y_block a b c d y h 2,
    brc_inverse_y_block a b c d y h 3)
   =
   y_inv_of
     ((a,b,c,d),
      (y (4*h),
       y (4*h+1),
       y (4*h+2),
       y (4*h+3)))"
  unfolding brc_inverse_y_block_def
    brc_tuple_component_def
  by (cases
      "y_inv_of
        ((a,b,c,d),
         (y (4*h),
          y (4*h+1),
          y (4*h+2),
          y (4*h+3)))")
     simp

lemma brc_inverse_y_block_forward:
  assumes nz:
    "a^2 + b^2 + c^2 + d^2 ≠ 0"
  shows
    "y_of
      ((a,b,c,d),
       (brc_inverse_y_block a b c d y h 0,
        brc_inverse_y_block a b c d y h 1,
        brc_inverse_y_block a b c d y h 2,
        brc_inverse_y_block a b c d y h 3))
     =
     (y (4*h),
      y (4*h+1),
      y (4*h+2),
      y (4*h+3))"
proof -
  have inverse:
    "y_of
      ((a,b,c,d),
       y_inv_of
        ((a,b,c,d),
         (y (4*h),
          y (4*h+1),
          y (4*h+2),
          y (4*h+3))))
     =
     (y (4*h),
      y (4*h+1),
      y (4*h+2),
      y (4*h+3))"
    using y_inverses_part_2[
      OF nz,
      of "y (4*h)"
         "y (4*h+1)"
         "y (4*h+2)"
         "y (4*h+3)"]
    by simp

  show ?thesis
    using inverse brc_inverse_y_block_tuple[
      where a = a and b = b and c = c and d = d
        and y = y and h = h]
    by simp
qed

lemma brc_x_from_y_plus_block_sqsum:
  assumes v_form:
    "𝗏 = 4 * w + 1"
  assumes h_lt:
    "h < w"
  assumes nz:
    "a^2 + b^2 + c^2 + d^2 ≠ 0"
  shows
    "y_block_sqsum a b c d
       (brc_x_from_y_plus a b c d w y) h
     =
     (y (4*h))^2 +
     (y (4*h+1))^2 +
     (y (4*h+2))^2 +
     (y (4*h+3))^2"
proof -
  let ?x =
    "brc_x_from_y_plus a b c d w y"

  have x0:
    "?x $$ (4*h,0)
     =
     brc_inverse_y_block a b c d y h 0"
    using brc_x_from_y_plus_block[
      where w = w and h = h and j = 0
        and a = a and b = b and c = c and d = d
        and y = y,
      OF v_form h_lt]
    by simp

  have x1:
    "?x $$ (4*h+1,0)
     =
     brc_inverse_y_block a b c d y h 1"
    using brc_x_from_y_plus_block[
      where w = w and h = h and j = 1
        and a = a and b = b and c = c and d = d
        and y = y,
      OF v_form h_lt]
    by simp

  have x2:
    "?x $$ (4*h+2,0)
     =
     brc_inverse_y_block a b c d y h 2"
    using brc_x_from_y_plus_block[
      where w = w and h = h and j = 2
        and a = a and b = b and c = c and d = d
        and y = y,
      OF v_form h_lt]
    by simp

  have x3:
    "?x $$ (4*h+3,0)
     =
     brc_inverse_y_block a b c d y h 3"
    using brc_x_from_y_plus_block[
      where w = w and h = h and j = 3
        and a = a and b = b and c = c and d = d
        and y = y,
      OF v_form h_lt]
    by simp

  have forward:
    "y_of
      ((a,b,c,d),
       (?x $$ (4*h,0),
        ?x $$ (4*h+1,0),
        ?x $$ (4*h+2,0),
        ?x $$ (4*h+3,0)))
     =
     (y (4*h),
      y (4*h+1),
      y (4*h+2),
      y (4*h+3))"
    using brc_inverse_y_block_forward[
      where a = a and b = b and c = c and d = d
        and y = y and h = h,
      OF nz]
      x0 x1 x2 x3
    by simp

  show ?thesis
    unfolding y_block_sqsum_def
    using forward
    by simp
qed

lemma brc_x_from_y_plus_blocks_sqsum:
  assumes v_form:
    "𝗏 = 4 * w + 1"
  assumes nz:
    "a^2 + b^2 + c^2 + d^2 ≠ 0"
  shows
    "y_blocks_sqsum a b c d
       (brc_x_from_y_plus a b c d w y) w
     =
     (∑i∈{0..<4*w}. (y i)^2)"
proof -
  have blocks:
    "y_blocks_sqsum a b c d
       (brc_x_from_y_plus a b c d w y) w
     =
     (∑h∈{0..<w}.
        ((y (4*h))^2 +
         (y (4*h+1))^2 +
         (y (4*h+2))^2 +
         (y (4*h+3))^2))"
  proof -
    show ?thesis
      unfolding y_blocks_sqsum_def
      apply (rule sum.cong)
       apply (rule refl)
    using brc_x_from_y_plus_block_sqsum[
      where w = w and a = a and b = b
        and c = c and d = d and y = y,
      OF v_form _ nz]
      by auto
  qed

  have regroup:
    "(∑i∈{0..<4*w}. (y i)^2)
     =
     (∑h∈{0..<w}.
        ((y (4*h))^2 +
         (y (4*h+1))^2 +
         (y (4*h+2))^2 +
         (y (4*h+3))^2))"
    using sum_four_blocks[
      where w = w and f = "λi. (y i)^2"]
    .

  show ?thesis
    using blocks regroup
    by simp
qed

definition brc_plus_coeff ::
  "nat ⇒ nat ⇒ nat ⇒ nat ⇒ nat ⇒
   nat ⇒ nat ⇒ rat" where
  "brc_plus_coeff a b c d w r j =
     (if r < 𝗏 then
        brc_L
          (brc_x_from_y_plus
            a b c d w
            (rat_unit_coordinate j))
          r
      else
        brc_y0
          (brc_x_from_y_plus
            a b c d w
            (rat_unit_coordinate j))
          w)"

definition brc_plus_weight ::
  "nat ⇒ rat" where
  "brc_plus_weight r =
     (if r < 𝗏 then 1 else - of_nat Λ)"

definition brc_plus_diagonal ::
  "nat ⇒ rat" where
  "brc_plus_diagonal j =
     (if j < 𝗏 - 1 then
        1
      else
        of_nat (𝗄 - Λ))"

lemma brc_plus_weight_L:
  assumes r_lt:
    "r < 𝗏"
  shows
    "brc_plus_weight r = 1"
  using r_lt
  unfolding brc_plus_weight_def
  by simp

lemma brc_plus_weight_y0:
  "brc_plus_weight 𝗏 = - of_nat Λ"
  unfolding brc_plus_weight_def
  by simp

lemma brc_plus_diagonal_unit:
  assumes j_lt:
    "j < 𝗏 - 1"
  shows
    "brc_plus_diagonal j = 1"
  using j_lt
  unfolding brc_plus_diagonal_def
  by simp

lemma brc_plus_diagonal_last:
  assumes v_pos:
    "0 < 𝗏"
  shows
    "brc_plus_diagonal (𝗏 - 1)
     =
     of_nat (𝗄 - Λ)"
  using v_pos
  unfolding brc_plus_diagonal_def
  by simp

lemma brc_inverse_y_block_add:
  "brc_inverse_y_block a b c d
      (λi. y i + z i) h j
   =
   brc_inverse_y_block a b c d y h j
   +
   brc_inverse_y_block a b c d z h j"
proof (cases "j = 0")
  case True

  show ?thesis
    using True
    unfolding brc_inverse_y_block_def
      brc_tuple_component_def
    apply (simp only:
        True if_True
        y_inv_of.simps
        y_inv_reversible.simps
        snd_conv
        one_of.simps)
    apply (subst add_divide_distrib[symmetric])
    apply (simp add: algebra_simps)
    done
next
  case False

  show ?thesis
  proof (cases "j = 1")
    case True

    show ?thesis
      using False True
      unfolding brc_inverse_y_block_def
        brc_tuple_component_def
      apply (simp only:
          False True
          if_False if_True
          y_inv_of.simps
          y_inv_reversible.simps
          snd_conv
          two_of.simps)
      apply (subst add_divide_distrib[symmetric])
      apply (simp add: algebra_simps)
      done
  next
    case False1: False

    show ?thesis
    proof (cases "j = 2")
      case True2: True

      show ?thesis
        using False False1 True2
        unfolding brc_inverse_y_block_def
          brc_tuple_component_def
        apply (simp only:
            False False1 True2
            if_False if_True
            y_inv_of.simps
            y_inv_reversible.simps
            snd_conv
            three_of.simps)
        apply (subst add_divide_distrib[symmetric])
        apply (simp add: algebra_simps)
        done
    next
      case False2: False

      show ?thesis
        using False False1 False2
        unfolding brc_inverse_y_block_def
          brc_tuple_component_def
        apply (simp only:
            False False1 False2
            if_False
            y_inv_of.simps
            y_inv_reversible.simps
            snd_conv
            four_of.simps)
        apply (subst add_divide_distrib[symmetric])
        apply (simp add: algebra_simps)
        done
    qed
  qed
qed

lemma brc_inverse_y_block_scale:
  "brc_inverse_y_block a b c d
      (λi. u * y i) h j
   =
   u * brc_inverse_y_block a b c d y h j"
  unfolding brc_inverse_y_block_def
    brc_tuple_component_def
  by (auto simp:
      algebra_simps)

lemma brc_x_from_y_plus_add:
  assumes i_bound:
    "i < 𝗏"
  shows
    "brc_x_from_y_plus a b c d w
       (λj. y j + z j) $$ (i,0)
     =
     brc_x_from_y_plus a b c d w y $$ (i,0)
     +
     brc_x_from_y_plus a b c d w z $$ (i,0)"
proof (cases "i < 4*w")
  case True

  show ?thesis
    unfolding brc_x_from_y_plus_def
    using i_bound True
      brc_inverse_y_block_add[
        where a = a and b = b and c = c and d = d
          and y = y and z = z
          and h = "i div 4" and j = "i mod 4"]
    by simp
next
  case False

  show ?thesis
    unfolding brc_x_from_y_plus_def
    using i_bound False
    by simp
qed

lemma brc_x_from_y_plus_scale:
  assumes i_bound:
    "i < 𝗏"
  shows
    "brc_x_from_y_plus a b c d w
       (λj. u * y j) $$ (i,0)
     =
     u *
     brc_x_from_y_plus a b c d w y $$ (i,0)"
proof (cases "i < 4*w")
  case True

  show ?thesis
    unfolding brc_x_from_y_plus_def
    using i_bound True
      brc_inverse_y_block_scale[
        where a = a and b = b and c = c and d = d
          and u = u and y = y
          and h = "i div 4" and j = "i mod 4"]
    by simp
next
  case False

  show ?thesis
    unfolding brc_x_from_y_plus_def
    using i_bound False
    by simp
qed

lemma brc_x_from_y_plus_zero:
  assumes i_bound:
    "i < 𝗏"
  shows
    "brc_x_from_y_plus a b c d w
       rat_vec_zero $$ (i,0)
     =
     0"
proof -
  have scaled:
    "brc_x_from_y_plus a b c d w
       (λj. (0::rat) * rat_vec_zero j) $$ (i,0)
     =
     (0::rat) *
     brc_x_from_y_plus a b c d w
       rat_vec_zero $$ (i,0)"
    using brc_x_from_y_plus_scale[
      where i = i and a = a and b = b
        and c = c and d = d and w = w
        and u = 0 and y = rat_vec_zero,
      OF i_bound]
    .

  show ?thesis
    using scaled
    unfolding rat_vec_zero_def
    by simp
qed

lemma brc_x_from_y_plus_sum:
  assumes finite:
    "finite S"
  assumes i_bound:
    "i < 𝗏"
  shows
    "brc_x_from_y_plus a b c d w
       (λt. ∑j∈S. f j t) $$ (i,0)
     =
     (∑j∈S.
        brc_x_from_y_plus a b c d w
          (f j) $$ (i,0))"
  using finite
proof (induction S rule: finite_induct)
  case empty

  show ?case
    using brc_x_from_y_plus_zero[
      where i = i and a = a and b = b
        and c = c and d = d and w = w,
      OF i_bound]
    unfolding rat_vec_zero_def
    by simp
next
  case (insert j S)

  have add:
    "brc_x_from_y_plus a b c d w
       (λt. f j t + (∑k∈S. f k t)) $$ (i,0)
     =
     brc_x_from_y_plus a b c d w
       (f j) $$ (i,0)
     +
     brc_x_from_y_plus a b c d w
       (λt. ∑k∈S. f k t) $$ (i,0)"
    using brc_x_from_y_plus_add[
      where i = i and a = a and b = b
        and c = c and d = d and w = w
        and y = "f j"
        and z = "λt. ∑k∈S. f k t",
      OF i_bound]
    .

  show ?case
    using insert add
    by simp
qed

definition rat_basis_expansion ::
  "nat ⇒ (nat ⇒ rat) ⇒ nat ⇒ rat" where
  "rat_basis_expansion n y =
     (λt.
        ∑j∈{0..<n}.
          y j * rat_unit_coordinate j t)"

lemma rat_basis_expansion_inside:
  assumes t_bound:
    "t < n"
  shows
    "rat_basis_expansion n y t = y t"
proof -
  have t_mem:
    "t ∈ {0..<n}"
    using t_bound
    by simp

  have finite:
    "finite {0..<n}"
    by simp

  have split:
    "(∑j∈{0..<n}.
       y j * rat_unit_coordinate j t)
     =
     y t * rat_unit_coordinate t t +
     (∑j∈{0..<n} - {t}.
        y j * rat_unit_coordinate j t)"
    using sum.remove[
      OF finite t_mem,
      of "λj. y j * rat_unit_coordinate j t"]
    by simp

  have unit_at:
    "rat_unit_coordinate t t = 1"
    unfolding rat_unit_coordinate_def
    by simp

  have rest_zero:
    "(∑j∈{0..<n} - {t}.
       y j * rat_unit_coordinate j t)
     =
     0"
  proof -
    show ?thesis
      apply (rule sum.neutral)
      unfolding rat_unit_coordinate_def
      by auto
  qed

  show ?thesis
    unfolding rat_basis_expansion_def
    using split unit_at rest_zero
    by simp
qed

lemma brc_x_from_y_plus_cong:
  assumes v_form:
    "𝗏 = 4 * w + 1"
  assumes i_bound:
    "i < 𝗏"
  assumes agree:
    "⋀t. t < 𝗏 ⟹ y t = z t"
  shows
    "brc_x_from_y_plus a b c d w y $$ (i,0)
     =
     brc_x_from_y_plus a b c d w z $$ (i,0)"
proof (cases "i < 4*w")
  case True

  let ?h = "i div 4"

  have h_lt:
    "?h < w"
    using True
    by (simp add: div_less_iff_less_mult)

  have b0:
    "4*?h < 𝗏"
    using h_lt v_form
    by simp

  have b1:
    "4*?h+1 < 𝗏"
    using h_lt v_form
    by simp

  have b2:
    "4*?h+2 < 𝗏"
    using h_lt v_form
    by simp

  have b3:
    "4*?h+3 < 𝗏"
    using h_lt v_form
    by simp

  have y0:
    "y (4*?h) = z (4*?h)"
    using agree[OF b0] .

  have y1:
    "y (4*?h+1) = z (4*?h+1)"
    using agree[OF b1] .

  have y2:
    "y (4*?h+2) = z (4*?h+2)"
    using agree[OF b2] .

  have y3:
    "y (4*?h+3) = z (4*?h+3)"
    using agree[OF b3] .

  show ?thesis
    unfolding brc_x_from_y_plus_def
      brc_inverse_y_block_def
    using i_bound True y0 y1 y2 y3
    by simp
next
  case False

  have yi:
    "y i = z i"
    using agree[OF i_bound] .

  show ?thesis
    unfolding brc_x_from_y_plus_def
    using i_bound False yi
    by simp
qed

lemma brc_x_from_y_plus_basis:
  assumes v_form:
    "𝗏 = 4 * w + 1"
  assumes i_bound:
    "i < 𝗏"
  shows
    "brc_x_from_y_plus a b c d w y $$ (i,0)
     =
     brc_x_from_y_plus a b c d w
       (rat_basis_expansion 𝗏 y) $$ (i,0)"
proof -
  have agree:
    "⋀t. t < 𝗏 ⟹
       y t = rat_basis_expansion 𝗏 y t"
  proof -
    fix t
    assume t_bound:
      "t < 𝗏"

    show
      "y t = rat_basis_expansion 𝗏 y t"
      using rat_basis_expansion_inside[
        where n = 𝗏 and y = y and t = t,
        OF t_bound]
      by simp
  qed

  show ?thesis
    using brc_x_from_y_plus_cong[
      where i = i
        and a = a and b = b and c = c and d = d
        and w = w
        and y = y
        and z = "rat_basis_expansion 𝗏 y",
      OF v_form i_bound agree]
    .
qed

lemma brc_x_from_y_plus_linear_expansion:
  assumes v_form:
    "𝗏 = 4 * w + 1"
  assumes i_bound:
    "i < 𝗏"
  shows
    "brc_x_from_y_plus a b c d w y $$ (i,0)
     =
     (∑j∈{0..<𝗏}.
        y j *
        brc_x_from_y_plus a b c d w
          (rat_unit_coordinate j) $$ (i,0))"
proof -
  have basis:
    "brc_x_from_y_plus a b c d w y $$ (i,0)
     =
     brc_x_from_y_plus a b c d w
       (rat_basis_expansion 𝗏 y) $$ (i,0)"
    using brc_x_from_y_plus_basis[
      where i = i
        and a = a and b = b and c = c and d = d
        and w = w and y = y,
      OF v_form i_bound]
    .

  have summed:
    "brc_x_from_y_plus a b c d w
       (rat_basis_expansion 𝗏 y) $$ (i,0)
     =
     (∑j∈{0..<𝗏}.
        brc_x_from_y_plus a b c d w
          (λt. y j * rat_unit_coordinate j t)
          $$ (i,0))"
    unfolding rat_basis_expansion_def
    using brc_x_from_y_plus_sum[
      where S = "{0..<𝗏}"
        and i = i
        and a = a and b = b and c = c and d = d
        and w = w
        and f = "λj t. y j * rat_unit_coordinate j t",
      OF _ i_bound]
    by simp

  have scaled:
    "(∑j∈{0..<𝗏}.
       brc_x_from_y_plus a b c d w
         (λt. y j * rat_unit_coordinate j t)
         $$ (i,0))
     =
     (∑j∈{0..<𝗏}.
       y j *
       brc_x_from_y_plus a b c d w
         (rat_unit_coordinate j) $$ (i,0))"
  proof -
    show ?thesis
      apply (rule sum.cong)
       apply (rule refl)
      using brc_x_from_y_plus_scale[
        where i = i
          and a = a and b = b and c = c and d = d
          and w = w]
        i_bound
      by simp
  qed

  show ?thesis
    using basis summed scaled
    by simp
qed

lemma brc_plus_coeff_L_representation:
  assumes v_form:
    "𝗏 = 4 * w + 1"
  assumes r_bound:
    "r < 𝗏"
  shows
    "brc_L
       (brc_x_from_y_plus a b c d w y) r
     =
     rat_linear_form 𝗏
       (brc_plus_coeff a b c d w r)
       y"
proof -
  let ?X =
    "brc_x_from_y_plus a b c d w"

  have entry:
    "?X y $$ (h,0)
     =
     (∑j∈{0..<𝗏}.
        y j *
        ?X (rat_unit_coordinate j) $$ (h,0))"
    if h_bound:
      "h ∈ {0..<𝗏}"
    for h
    using brc_x_from_y_plus_linear_expansion[
      where i = h
        and a = a and b = b and c = c and d = d
        and w = w and y = y,
      OF v_form]
      h_bound
    by simp

  have expanded:
    "brc_L (?X y) r
     =
     (∑h∈{0..<𝗏}.
        of_int (N $$ (h,r)) *
        (∑j∈{0..<𝗏}.
           y j *
           ?X (rat_unit_coordinate j) $$ (h,0)))"
    unfolding brc_L_def
    using entry
    by (intro sum.cong) auto

  also have
    "... =
     (∑h∈{0..<𝗏}.
        ∑j∈{0..<𝗏}.
          of_int (N $$ (h,r)) *
          (y j *
           ?X (rat_unit_coordinate j) $$ (h,0)))"
    by (simp only: sum_distrib_left)

  also have
    "... =
     (∑j∈{0..<𝗏}.
        ∑h∈{0..<𝗏}.
          of_int (N $$ (h,r)) *
          (y j *
           ?X (rat_unit_coordinate j) $$ (h,0)))"
    by (rule sum.swap)

  also have
    "... =
     (∑j∈{0..<𝗏}.
        y j *
        (∑h∈{0..<𝗏}.
           of_int (N $$ (h,r)) *
           ?X (rat_unit_coordinate j) $$ (h,0)))"
    apply (rule sum.cong)
     apply (rule refl)
    apply (simp add:
        sum_distrib_left
        mult.assoc
        mult.left_commute
        mult.commute)
    done

  also have
    "... =
     (∑j∈{0..<𝗏}.
        y j *
        brc_L
          (?X (rat_unit_coordinate j)) r)"
    unfolding brc_L_def
    by simp

  also have
    "... =
     (∑j∈{0..<𝗏}.
        brc_plus_coeff a b c d w r j *
        y j)"
  proof -
    show ?thesis
      apply (rule sum.cong)
       apply (rule refl)
    using r_bound
      unfolding brc_plus_coeff_def
      by (simp add: mult.commute)
  qed

  also have
    "... =
     rat_linear_form 𝗏
       (brc_plus_coeff a b c d w r)
       y"
    unfolding rat_linear_form_def
    by simp

  finally show ?thesis .
qed

lemma brc_y0_as_full_sum:
  assumes v_form:
    "𝗏 = 4 * w + 1"
  shows
    "brc_y0 x w
     =
     (∑h∈{0..<𝗏}. x $$ (h,0))"
proof -
  have split:
    "(∑h∈{0..<𝗏}. x $$ (h,0))
     =
     (∑h∈{0..<4*w}. x $$ (h,0))
     + x $$ (4*w,0)"
    using brc_x_sum_split_4w_last_plain[
      OF v_form, of x]
    .

  show ?thesis
    unfolding brc_y0_def
      x_head_sum_def x_last_def
    using split
    by simp
qed

lemma brc_plus_coeff_y0_representation:
  assumes v_form:
    "𝗏 = 4 * w + 1"
  shows
    "brc_y0
       (brc_x_from_y_plus a b c d w y) w
     =
     rat_linear_form 𝗏
       (brc_plus_coeff a b c d w 𝗏)
       y"
proof -
  let ?X =
    "brc_x_from_y_plus a b c d w"

  have entry:
    "?X y $$ (h,0)
     =
     (∑j∈{0..<𝗏}.
        y j *
        ?X (rat_unit_coordinate j) $$ (h,0))"
    if h_mem:
      "h ∈ {0..<𝗏}"
    for h
    using brc_x_from_y_plus_linear_expansion[
      where i = h
        and a = a and b = b and c = c and d = d
        and w = w and y = y,
      OF v_form]
      h_mem
    by simp

  have expanded:
    "brc_y0 (?X y) w
     =
     (∑h∈{0..<𝗏}.
        ∑j∈{0..<𝗏}.
          y j *
          ?X (rat_unit_coordinate j) $$ (h,0))"
    unfolding brc_y0_as_full_sum[OF v_form]
    using entry
    by (intro sum.cong) auto

  also have
    "... =
     (∑j∈{0..<𝗏}.
        ∑h∈{0..<𝗏}.
          y j *
          ?X (rat_unit_coordinate j) $$ (h,0))"
    by (rule sum.swap)

  also have
    "... =
     (∑j∈{0..<𝗏}.
        y j *
        (∑h∈{0..<𝗏}.
           ?X (rat_unit_coordinate j) $$ (h,0)))"
  proof (rule sum.cong)
    show "{0..<𝗏} = {0..<𝗏}"
      by simp
  next
    fix j
    assume j_mem:
      "j ∈ {0..<𝗏}"

    show
      "(∑h∈{0..<𝗏}.
         y j *
         ?X (rat_unit_coordinate j) $$ (h,0))
       =
       y j *
       (∑h∈{0..<𝗏}.
          ?X (rat_unit_coordinate j) $$ (h,0))"
      by (metis sum_distrib_left)
  qed

  also have
    "... =
     (∑j∈{0..<𝗏}.
        y j *
        brc_y0
          (?X (rat_unit_coordinate j)) w)"
    using brc_y0_as_full_sum[OF v_form]
    by simp

  also have
    "... =
     (∑j∈{0..<𝗏}.
        brc_plus_coeff a b c d w 𝗏 j *
        y j)"
    unfolding brc_plus_coeff_def
    by (intro sum.cong) (auto simp: mult.commute)

  also have
    "... =
     rat_linear_form 𝗏
       (brc_plus_coeff a b c d w 𝗏)
       y"
    unfolding rat_linear_form_def
    by simp

  finally show ?thesis .
qed

lemma brc_plus_weighted_initial:
  assumes v_form:
    "𝗏 = 4 * w + 1"
  assumes abcd:
    "𝗄 - Λ = a^2 + b^2 + c^2 + d^2"
  shows
    "⋀y.
       rat_weighted_linear_squares_from
         𝗏 0 (𝗏 + 1)
         brc_plus_weight
         (brc_plus_coeff a b c d w)
         y
       =
       rat_diagonal_form 𝗏
         brc_plus_diagonal y"
proof -
  fix y

  let ?X =
    "brc_x_from_y_plus a b c d w y"

  have diff_nz:
    "𝗄 - Λ ≠ 0"
    using blocksize_gt_index
    by simp

  have nz:
    "a^2 + b^2 + c^2 + d^2 ≠ 0"
    using abcd diff_nz
    by metis

  have transformed:
    "(∑r∈{0..<𝗏}. (brc_L ?X r)^2)
     =
     of_nat Λ * (brc_y0 ?X w)^2
     +
     y_blocks_sqsum a b c d ?X w
     +
     of_nat (𝗄 - Λ) * (brc_yv ?X w)^2"
    using brc_x_equation_transformed_named[
      where w = w and a = a and b = b and c = c and d = d
        and x = ?X,
      OF v_form abcd]
    .

  have blocks:
    "y_blocks_sqsum a b c d ?X w
     =
     (∑j∈{0..<𝗏 - 1}. (y j)^2)"
  proof -
    have recovered:
      "y_blocks_sqsum a b c d ?X w
       =
       (∑j∈{0..<4*w}. (y j)^2)"
      using brc_x_from_y_plus_blocks_sqsum[
        where w = w and a = a and b = b
          and c = c and d = d and y = y,
        OF v_form nz]
      .

    have range:
      "4*w = 𝗏 - 1"
      using v_form
      by simp

    show ?thesis
      using recovered range
      by simp
  qed

  have last:
    "brc_yv ?X w = y (𝗏 - 1)"
  proof -
    have entry:
      "?X $$ (4*w,0) = y (4*w)"
      using brc_x_from_y_plus_last[
        where w = w and a = a and b = b
          and c = c and d = d and y = y,
        OF v_form]
      .

    show ?thesis
      unfolding brc_yv_def x_last_def
      using entry v_form
      by simp
  qed

  have L_forms:
    "(∑r∈{0..<𝗏}.
       (rat_linear_form 𝗏
          (brc_plus_coeff a b c d w r) y)^2)
     =
     (∑r∈{0..<𝗏}. (brc_L ?X r)^2)"
  proof -
    show ?thesis
      apply (rule sum.cong)
       apply (rule refl)
    using brc_plus_coeff_L_representation[
      where w = w and a = a and b = b
        and c = c and d = d and y = y,
      OF v_form]
      by auto
  qed

  have y0_form:
    "rat_linear_form 𝗏
       (brc_plus_coeff a b c d w 𝗏) y
     =
     brc_y0 ?X w"
    using brc_plus_coeff_y0_representation[
      where w = w and a = a and b = b
        and c = c and d = d and y = y,
      OF v_form]
    by simp

  have weighted:
    "rat_weighted_linear_squares_from
       𝗏 0 (𝗏 + 1)
       brc_plus_weight
       (brc_plus_coeff a b c d w) y
     =
     (∑r∈{0..<𝗏}. (brc_L ?X r)^2)
     -
     of_nat Λ * (brc_y0 ?X w)^2"
  proof -
    have split:
      "(∑r∈{0..<𝗏 + 1}.
         brc_plus_weight r *
         (rat_linear_form 𝗏
           (brc_plus_coeff a b c d w r) y)^2)
       =
       (∑r∈{0..<𝗏}.
          brc_plus_weight r *
          (rat_linear_form 𝗏
            (brc_plus_coeff a b c d w r) y)^2)
       +
       brc_plus_weight 𝗏 *
         (rat_linear_form 𝗏
           (brc_plus_coeff a b c d w 𝗏) y)^2"
      by (simp add: sum.atLeastLessThan_Suc)

    show ?thesis
      unfolding rat_weighted_linear_squares_from_def
      using split L_forms y0_form
      unfolding brc_plus_weight_def
      by simp
  qed

  have diagonal:
    "rat_diagonal_form 𝗏 brc_plus_diagonal y
     =
     (∑j∈{0..<𝗏 - 1}. (y j)^2)
     +
     of_nat (𝗄 - Λ) * (y (𝗏 - 1))^2"
  proof -
    have v_pos:
      "0 < 𝗏"
      using v_form
      by simp

    obtain t where v_eq:
      "𝗏 = Suc t"
      using v_pos
      by (cases 𝗏) auto

    show ?thesis
      unfolding rat_diagonal_form_def
        brc_plus_diagonal_def
      using v_eq
      by (simp add: sum.atLeastLessThan_Suc)
  qed

  have rearranged:
    "(∑r∈{0..<𝗏}. (brc_L ?X r)^2)
     -
     of_nat Λ * (brc_y0 ?X w)^2
     =
     (∑j∈{0..<𝗏 - 1}. (y j)^2)
     +
     of_nat (𝗄 - Λ) * (y (𝗏 - 1))^2"
  proof -
    have
      "(∑r∈{0..<𝗏}. (brc_L ?X r)^2)
       =
       of_nat Λ * (brc_y0 ?X w)^2
       +
       (∑j∈{0..<𝗏 - 1}. (y j)^2)
       +
       of_nat (𝗄 - Λ) * (y (𝗏 - 1))^2"
      using transformed blocks last
      by simp

    then show ?thesis
      by simp
  qed

  show
    "rat_weighted_linear_squares_from
       𝗏 0 (𝗏 + 1)
       brc_plus_weight
       (brc_plus_coeff a b c d w) y
     =
     rat_diagonal_form 𝗏
       brc_plus_diagonal y"
    using weighted diagonal rearranged
    by simp
qed

lemma brc_plus_rational_solution:
  assumes v_form:
    "𝗏 = 4 * w + 1"
  assumes abcd:
    "𝗄 - Λ = a^2 + b^2 + c^2 + d^2"
  shows
    "∃x y z :: rat.
       (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧
       x^2 =
         of_nat (𝗄 - Λ) * y^2 +
         of_nat Λ * z^2"
proof -
  have v_pos:
    "0 < 𝗏"
    using v_non_zero
    by simp

  have weights:
    "⋀q. q < 𝗏 ⟹ brc_plus_weight q = 1"
    using brc_plus_weight_L
    by blast

  have carried:
    "brc_plus_weight 𝗏 = - of_nat Λ"
    using brc_plus_weight_y0 .

  have units:
    "⋀q. q < 𝗏 - 1 ⟹
       brc_plus_diagonal q = 1"
    using brc_plus_diagonal_unit
    by blast

  have last:
    "brc_plus_diagonal (𝗏 - 1)
     =
     of_nat (𝗄 - Λ)"
    using brc_plus_diagonal_last[
      OF v_pos]
    .

  have initial:
    "⋀u.
       rat_weighted_linear_squares_from
         𝗏 0 (𝗏 + 1)
         brc_plus_weight
         (brc_plus_coeff a b c d w)
         u
       =
       rat_diagonal_form 𝗏
         brc_plus_diagonal u"
    using brc_plus_weighted_initial[
      OF v_form abcd]
    .

  show ?thesis
    using rat_weighted_elimination_nontrivial_solution[
      where n = 𝗏
        and C = "brc_plus_coeff a b c d w"
        and d = brc_plus_diagonal
        and W = brc_plus_weight
        and lam = "of_nat Λ"
        and delta = "of_nat (𝗄 - Λ)",
      OF v_pos weights carried units last initial]
    .
qed

lemma rat_weighted_elimination_terminal_general:
  fixes C :: "nat ⇒ nat ⇒ rat"
  fixes d W :: "nat ⇒ rat"
  fixes alpha beta delta :: rat
  assumes n_pos:
    "0 < n"
  assumes elimination_weights:
    "⋀q. q < n - 1 ⟹ W q = 1"
  assumes first_terminal_weight:
    "W (n - 1) = alpha"
  assumes second_terminal_weight:
    "W n = beta"
  assumes unit_diagonal:
    "⋀q. q < n - 1 ⟹ d q = 1"
  assumes last_diagonal:
    "d (n - 1) = delta"
  assumes initial:
    "⋀x.
       rat_weighted_linear_squares_from
         n 0 (n + 1) W C x
       =
       rat_diagonal_form n d x"
  shows
    "⋀y.
       alpha *
       (rat_linear_form n
          (rat_elimination_coeffs
            n (n - 1) C (n - 1))
          y)^2
       +
       beta *
       (rat_linear_form n
          (rat_elimination_coeffs
            n (n - 1) C n)
          y)^2
       =
       delta * (y (n - 1))^2"
proof -
  fix y

  have iterated:
    "rat_weighted_linear_squares_from
       n (n - 1) (n + 1) W
       (rat_elimination_coeffs n (n - 1) C) y
     =
     rat_diagonal_form n d
       (rat_zero_prefix (n - 1) y)"
    using rat_weighted_elimination_iterate[
      where n = n
        and Q = "n - 1"
        and m = "n + 1"
        and W = W
        and C = C
        and d = d,
      OF _ _ elimination_weights
         unit_diagonal initial]
    by simp

  have left:
    "rat_weighted_linear_squares_from
       n (n - 1) (n + 1) W
       (rat_elimination_coeffs n (n - 1) C) y
     =
     alpha *
       (rat_linear_form n
          (rat_elimination_coeffs
            n (n - 1) C (n - 1))
          y)^2
     +
     beta *
       (rat_linear_form n
          (rat_elimination_coeffs
            n (n - 1) C n)
          y)^2"
    using rat_weighted_terminal_two[
      where n = n
        and W = W
        and C = "rat_elimination_coeffs n (n - 1) C"
        and y = y,
      OF n_pos]
      first_terminal_weight second_terminal_weight
    by simp

  have right:
    "rat_diagonal_form n d
       (rat_zero_prefix (n - 1) y)
     =
     delta * (y (n - 1))^2"
    using rat_diagonal_form_zero_prefix_last[
      where n = n and d = d and y = y,
      OF n_pos]
      last_diagonal
    by simp

  show
    "alpha *
       (rat_linear_form n
          (rat_elimination_coeffs
            n (n - 1) C (n - 1))
          y)^2
     +
     beta *
       (rat_linear_form n
          (rat_elimination_coeffs
            n (n - 1) C n)
          y)^2
     =
     delta * (y (n - 1))^2"
    using iterated left right
    by simp
qed

lemma rat_weighted_elimination_terminal_solution_general:
  fixes C :: "nat ⇒ nat ⇒ rat"
  fixes d W :: "nat ⇒ rat"
  fixes alpha beta :: rat
  assumes n_pos:
    "0 < n"
  assumes elimination_weights:
    "⋀q. q < n - 1 ⟹ W q = 1"
  assumes first_terminal_weight:
    "W (n - 1) = alpha"
  assumes second_terminal_weight:
    "W n = beta"
  assumes unit_diagonal:
    "⋀q. q < n - 1 ⟹ d q = 1"
  assumes last_diagonal:
    "d (n - 1) = 1"
  assumes initial:
    "⋀x.
       rat_weighted_linear_squares_from
         n 0 (n + 1) W C x
       =
       rat_diagonal_form n d x"
  shows
    "∃x y z :: rat.
       (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧
       x^2 = alpha * y^2 + beta * z^2"
proof -
  let ?u =
    "rat_unit_coordinate (n - 1)"

  let ?y =
    "rat_linear_form n
       (rat_elimination_coeffs
         n (n - 1) C (n - 1))
       ?u"

  let ?z =
    "rat_linear_form n
       (rat_elimination_coeffs
         n (n - 1) C n)
       ?u"

  have general_terminal:
    "⋀v.
       alpha *
       (rat_linear_form n
          (rat_elimination_coeffs
            n (n - 1) C (n - 1))
          v)^2
       +
       beta *
       (rat_linear_form n
          (rat_elimination_coeffs
            n (n - 1) C n)
          v)^2
       =
       (v (n - 1))^2"
  proof -
    fix v

    have result:
      "alpha *
       (rat_linear_form n
          (rat_elimination_coeffs
            n (n - 1) C (n - 1))
          v)^2
       +
       beta *
       (rat_linear_form n
          (rat_elimination_coeffs
            n (n - 1) C n)
          v)^2
       =
       1 * (v (n - 1))^2"
    proof (rule rat_weighted_elimination_terminal_general[
        where n = n
          and C = C
          and d = d
          and W = W
          and alpha = alpha
          and beta = beta
          and delta = 1])
      show "0 < n"
        using n_pos .
      show "⋀q. q < n - 1 ⟹ W q = 1"
        using elimination_weights .
      show "W (n - 1) = alpha"
        using first_terminal_weight .
      show "W n = beta"
        using second_terminal_weight .
      show "⋀q. q < n - 1 ⟹ d q = 1"
        using unit_diagonal .
      show "d (n - 1) = 1"
        using last_diagonal .
      show
        "⋀x.
         rat_weighted_linear_squares_from
           n 0 (n + 1) W C x
         =
         rat_diagonal_form n d x"
        using initial .
    qed

    show
      "alpha *
       (rat_linear_form n
          (rat_elimination_coeffs
            n (n - 1) C (n - 1))
          v)^2
       +
       beta *
       (rat_linear_form n
          (rat_elimination_coeffs
            n (n - 1) C n)
          v)^2
       =
       (v (n - 1))^2"
      using result
      by simp
  qed

  have terminal:
    "alpha * ?y^2 + beta * ?z^2
     =
     (?u (n - 1))^2"
    using general_terminal[of ?u]
    .

  have unit_value:
    "?u (n - 1) = 1"
    unfolding rat_unit_coordinate_def
    by simp

  have equation:
    "(1::rat)^2 = alpha * ?y^2 + beta * ?z^2"
    using terminal unit_value
    by simp

  have nonzero:
    "(1::rat) ≠ 0 ∨ ?y ≠ 0 ∨ ?z ≠ 0"
    by simp

  show ?thesis
    using equation nonzero
    by blast
qed

definition brc_x_from_y_minus ::
  "nat ⇒ nat ⇒ nat ⇒ nat ⇒
   nat ⇒ (nat ⇒ rat) ⇒ rat mat" where
  "brc_x_from_y_minus a b c d w y =
     mat 𝗏 1
       (λ(i,j).
          if j ≠ 0 then 0
          else
            brc_inverse_y_block
              a b c d y
              (i div 4) (i mod 4))"

definition brc_xv1_from_y_minus ::
  "nat ⇒ nat ⇒ nat ⇒ nat ⇒
   nat ⇒ (nat ⇒ rat) ⇒ rat" where
  "brc_xv1_from_y_minus a b c d w y =
     brc_inverse_y_block
       a b c d y
       ((𝗏) div 4) ((𝗏) mod 4)"

definition brc_minus_coeff ::
  "nat ⇒ nat ⇒ nat ⇒ nat ⇒ nat ⇒
   nat ⇒ nat ⇒ rat" where
  "brc_minus_coeff a b c d w r j =
     (if r < 𝗏 then
        brc_L
          (brc_x_from_y_minus
            a b c d w
            (rat_unit_coordinate j))
          r
      else if r = 𝗏 then
        brc_xv1_from_y_minus
          a b c d w
          (rat_unit_coordinate j)
      else
        t_of
          (brc_x_from_y_minus
            a b c d w
            (rat_unit_coordinate j)))"

definition brc_minus_diagonal ::
  "nat ⇒ rat" where
  "brc_minus_diagonal j = 1"

definition brc_minus_weight ::
  "nat ⇒ rat" where
  "brc_minus_weight r =
     (if r < 𝗏 then
        1
      else if r = 𝗏 then
        of_nat (𝗄 - Λ)
      else
        - of_nat Λ)"

lemma brc_minus_weight_L:
  assumes r_lt:
    "r < 𝗏"
  shows
    "brc_minus_weight r = 1"
  using r_lt
  unfolding brc_minus_weight_def
  by simp

lemma brc_minus_weight_xv1:
  "brc_minus_weight 𝗏 =
   of_nat (𝗄 - Λ)"
  unfolding brc_minus_weight_def
  by simp

lemma brc_minus_weight_y0:
  "brc_minus_weight (𝗏 + 1) =
   - of_nat Λ"
  unfolding brc_minus_weight_def
  by simp

lemma brc_minus_diagonal_one:
  "brc_minus_diagonal j = 1"
  unfolding brc_minus_diagonal_def
  by simp

lemma brc_x_from_y_minus_add:
  assumes i_bound:
    "i < 𝗏"
  shows
    "brc_x_from_y_minus a b c d w
       (λj. y j + z j) $$ (i,0)
     =
     brc_x_from_y_minus a b c d w y $$ (i,0)
     +
     brc_x_from_y_minus a b c d w z $$ (i,0)"
proof -
  show ?thesis
    unfolding brc_x_from_y_minus_def
    using i_bound
      brc_inverse_y_block_add[
        where a = a and b = b and c = c and d = d
          and y = y and z = z
          and h = "i div 4" and j = "i mod 4"]
    by simp
qed

lemma brc_x_from_y_minus_scale:
  assumes i_bound:
    "i < 𝗏"
  shows
    "brc_x_from_y_minus a b c d w
       (λj. u * y j) $$ (i,0)
     =
     u *
     brc_x_from_y_minus a b c d w y $$ (i,0)"
proof -
  show ?thesis
    unfolding brc_x_from_y_minus_def
    using i_bound
      brc_inverse_y_block_scale[
        where a = a and b = b and c = c and d = d
          and u = u and y = y
          and h = "i div 4" and j = "i mod 4"]
    by simp
qed

lemma brc_xv1_from_y_minus_add:
  "brc_xv1_from_y_minus a b c d w
      (λj. y j + z j)
   =
   brc_xv1_from_y_minus a b c d w y
   +
   brc_xv1_from_y_minus a b c d w z"
  unfolding brc_xv1_from_y_minus_def
  using brc_inverse_y_block_add[
    where a = a and b = b and c = c and d = d
      and y = y and z = z
      and h = "𝗏 div 4" and j = "𝗏 mod 4"]
  by simp

lemma brc_xv1_from_y_minus_scale:
  "brc_xv1_from_y_minus a b c d w
      (λj. u * y j)
   =
   u * brc_xv1_from_y_minus a b c d w y"
  unfolding brc_xv1_from_y_minus_def
  using brc_inverse_y_block_scale[
    where a = a and b = b and c = c and d = d
      and u = u and y = y
      and h = "𝗏 div 4" and j = "𝗏 mod 4"]
  by simp

definition brc_extended_x_from_y_minus ::
  "nat ⇒ nat ⇒ nat ⇒ nat ⇒ nat ⇒
   (nat ⇒ rat) ⇒ nat ⇒ rat" where
  "brc_extended_x_from_y_minus a b c d w y i =
     (if i < 𝗏 then
        brc_x_from_y_minus a b c d w y $$ (i,0)
      else
        brc_xv1_from_y_minus a b c d w y)"

lemma brc_extended_x_from_y_minus_add:
  assumes i_bound:
    "i < 𝗏 + 1"
  shows
    "brc_extended_x_from_y_minus a b c d w
       (λj. y j + z j) i
     =
     brc_extended_x_from_y_minus a b c d w y i
     +
     brc_extended_x_from_y_minus a b c d w z i"
proof (cases "i < 𝗏")
  case True

  show ?thesis
    unfolding brc_extended_x_from_y_minus_def
    using True
      brc_x_from_y_minus_add[
        where i = i and a = a and b = b
          and c = c and d = d and w = w
          and y = y and z = z,
        OF True]
    by simp
next
  case False

  have i_eq:
    "i = 𝗏"
    using i_bound False
    by simp

  show ?thesis
    unfolding brc_extended_x_from_y_minus_def
    using False i_eq
      brc_xv1_from_y_minus_add[
        where a = a and b = b and c = c and d = d
          and w = w and y = y and z = z]
    by simp
qed

lemma brc_extended_x_from_y_minus_scale:
  assumes i_bound:
    "i < 𝗏 + 1"
  shows
    "brc_extended_x_from_y_minus a b c d w
       (λj. u * y j) i
     =
     u *
     brc_extended_x_from_y_minus a b c d w y i"
proof (cases "i < 𝗏")
  case True

  show ?thesis
    unfolding brc_extended_x_from_y_minus_def
    using True
      brc_x_from_y_minus_scale[
        where i = i and a = a and b = b
          and c = c and d = d and w = w
          and u = u and y = y,
        OF True]
    by simp
next
  case False

  have i_eq:
    "i = 𝗏"
    using i_bound False
    by simp

  show ?thesis
    unfolding brc_extended_x_from_y_minus_def
    using False i_eq
      brc_xv1_from_y_minus_scale[
        where a = a and b = b and c = c and d = d
          and w = w and u = u and y = y]
    by simp
qed

lemma brc_extended_x_from_y_minus_zero:
  assumes i_bound:
    "i < 𝗏 + 1"
  shows
    "brc_extended_x_from_y_minus
       a b c d w rat_vec_zero i
     =
     0"
proof -
  have scaled:
    "brc_extended_x_from_y_minus a b c d w
       (λj. (0::rat) * rat_vec_zero j) i
     =
     (0::rat) *
     brc_extended_x_from_y_minus
       a b c d w rat_vec_zero i"
    using brc_extended_x_from_y_minus_scale[
      where i = i and a = a and b = b
        and c = c and d = d and w = w
        and u = 0 and y = rat_vec_zero,
      OF i_bound]
    .

  show ?thesis
    using scaled
    unfolding rat_vec_zero_def
    by simp
qed

lemma brc_extended_x_from_y_minus_sum:
  assumes finite:
    "finite S"
  assumes i_bound:
    "i < 𝗏 + 1"
  shows
    "brc_extended_x_from_y_minus a b c d w
       (λt. ∑j∈S. f j t) i
     =
     (∑j∈S.
        brc_extended_x_from_y_minus
          a b c d w (f j) i)"
  using finite
proof (induction S rule: finite_induct)
  case empty

  show ?case
    using brc_extended_x_from_y_minus_zero[
      where i = i and a = a and b = b
        and c = c and d = d and w = w,
      OF i_bound]
    unfolding rat_vec_zero_def
    by simp
next
  case (insert j S)

  have add:
    "brc_extended_x_from_y_minus a b c d w
       (λt. f j t + (∑k∈S. f k t)) i
     =
     brc_extended_x_from_y_minus a b c d w
       (f j) i
     +
     brc_extended_x_from_y_minus a b c d w
       (λt. ∑k∈S. f k t) i"
    using brc_extended_x_from_y_minus_add[
      where i = i and a = a and b = b
        and c = c and d = d and w = w
        and y = "f j"
        and z = "λt. ∑k∈S. f k t",
      OF i_bound]
    .

  show ?case
    using insert add
    by simp
qed

lemma brc_inverse_y_block_cong:
  assumes e0: "y (4*h) = z (4*h)"
  assumes e1: "y (4*h+1) = z (4*h+1)"
  assumes e2: "y (4*h+2) = z (4*h+2)"
  assumes e3: "y (4*h+3) = z (4*h+3)"
  shows
    "brc_inverse_y_block a b c d y h j
     =
     brc_inverse_y_block a b c d z h j"
  using e0 e1 e2 e3
  unfolding brc_inverse_y_block_def
  by simp

lemma brc_extended_x_from_y_minus_cong:
  assumes v_form:
    "𝗏 = 4 * w - 1"
  assumes w_pos:
    "0 < w"
  assumes i_bound:
    "i < 𝗏 + 1"
  assumes agree:
    "⋀t. t < 𝗏 + 1 ⟹ y t = z t"
  shows
    "brc_extended_x_from_y_minus a b c d w y i
     =
     brc_extended_x_from_y_minus a b c d w z i"
proof (cases "i < 𝗏")
  case True

  let ?h = "i div 4"

  have i_lt_4w:
    "i < 4*w"
    using True v_form w_pos
    by simp

  have h_lt:
    "?h < w"
    using i_lt_4w
    by (simp add: div_less_iff_less_mult)

  have b0:
    "4*?h < 𝗏 + 1"
    using h_lt v_form w_pos
    by simp

  have b1:
    "4*?h+1 < 𝗏 + 1"
    using h_lt v_form w_pos
    by simp

  have b2:
    "4*?h+2 < 𝗏 + 1"
    using h_lt v_form w_pos
    by simp

  have b3:
    "4*?h+3 < 𝗏 + 1"
    using h_lt v_form w_pos
    by simp

  have block:
    "brc_inverse_y_block a b c d y ?h (i mod 4)
     =
     brc_inverse_y_block a b c d z ?h (i mod 4)"
    using brc_inverse_y_block_cong[
      where a = a and b = b and c = c and d = d
        and y = y and z = z and h = ?h and j = "i mod 4",
      OF agree[OF b0] agree[OF b1]
         agree[OF b2] agree[OF b3]]
    .

  show ?thesis
    unfolding brc_extended_x_from_y_minus_def
      brc_x_from_y_minus_def
    using True block
    by simp
next
  case False

  have i_eq:
    "i = 𝗏"
    using i_bound False
    by simp

  have v_div:
    "𝗏 div 4 = w - 1"
    using v_form w_pos
    by simp

  obtain s where w_eq:
    "w = Suc s"
    using w_pos
    by (cases w) auto

  have v_eq:
    "𝗏 = 4*s + 3"
    using v_form w_eq
    by simp

  have v_mod:
    "𝗏 mod 4 = 3"
    using v_eq
    by simp

  have b0:
    "4*(w-1) < 𝗏 + 1"
    using v_form w_pos
    by simp

  have b1:
    "4*(w-1)+1 < 𝗏 + 1"
    using v_form w_pos
    by simp

  have b2:
    "4*(w-1)+2 < 𝗏 + 1"
    using v_form w_pos
    by simp

  have b3:
    "4*(w-1)+3 < 𝗏 + 1"
    using v_form w_pos
    by simp

  have block:
    "brc_xv1_from_y_minus a b c d w y
     =
     brc_xv1_from_y_minus a b c d w z"
    unfolding brc_xv1_from_y_minus_def
    using v_div v_mod
      brc_inverse_y_block_cong[
        where a = a and b = b and c = c and d = d
          and y = y and z = z and h = "w-1" and j = 3,
        OF agree[OF b0] agree[OF b1]
           agree[OF b2] agree[OF b3]]
    by simp

  show ?thesis
    unfolding brc_extended_x_from_y_minus_def
    using False i_eq block
    by simp
qed

lemma brc_extended_x_from_y_minus_basis:
  assumes v_form:
    "𝗏 = 4 * w - 1"
  assumes w_pos:
    "0 < w"
  assumes i_bound:
    "i < 𝗏 + 1"
  shows
    "brc_extended_x_from_y_minus a b c d w y i
     =
     brc_extended_x_from_y_minus a b c d w
       (rat_basis_expansion (𝗏 + 1) y) i"
proof -
  have agree:
    "⋀t. t < 𝗏 + 1 ⟹
       y t =
       rat_basis_expansion (𝗏 + 1) y t"
  proof -
    fix t
    assume t_bound:
      "t < 𝗏 + 1"

    show
      "y t =
       rat_basis_expansion (𝗏 + 1) y t"
      using rat_basis_expansion_inside[
        where n = "𝗏 + 1"
          and y = y and t = t,
        OF t_bound]
      by simp
  qed

  show ?thesis
    using brc_extended_x_from_y_minus_cong[
      where i = i
        and a = a and b = b and c = c and d = d
        and w = w
        and y = y
        and z = "rat_basis_expansion (𝗏 + 1) y",
      OF v_form w_pos i_bound agree]
    .
qed

lemma brc_extended_x_from_y_minus_linear_expansion:
  assumes v_form:
    "𝗏 = 4 * w - 1"
  assumes w_pos:
    "0 < w"
  assumes i_bound:
    "i < 𝗏 + 1"
  shows
    "brc_extended_x_from_y_minus a b c d w y i
     =
     (∑j∈{0..<𝗏 + 1}.
        y j *
        brc_extended_x_from_y_minus a b c d w
          (rat_unit_coordinate j) i)"
proof -
  have basis:
    "brc_extended_x_from_y_minus a b c d w y i
     =
     brc_extended_x_from_y_minus a b c d w
       (rat_basis_expansion (𝗏 + 1) y) i"
    using brc_extended_x_from_y_minus_basis[
      where i = i
        and a = a and b = b and c = c and d = d
        and w = w and y = y,
      OF v_form w_pos i_bound]
    .

  have summed:
    "brc_extended_x_from_y_minus a b c d w
       (rat_basis_expansion (𝗏 + 1) y) i
     =
     (∑j∈{0..<𝗏 + 1}.
        brc_extended_x_from_y_minus a b c d w
          (λt. y j * rat_unit_coordinate j t) i)"
    unfolding rat_basis_expansion_def
    using brc_extended_x_from_y_minus_sum[
      where S = "{0..<𝗏 + 1}"
        and i = i
        and a = a and b = b and c = c and d = d
        and w = w
        and f = "λj t.
          y j * rat_unit_coordinate j t",
      OF _ i_bound]
    by simp

  have scaled:
    "(∑j∈{0..<𝗏 + 1}.
       brc_extended_x_from_y_minus a b c d w
         (λt. y j * rat_unit_coordinate j t) i)
     =
     (∑j∈{0..<𝗏 + 1}.
       y j *
       brc_extended_x_from_y_minus a b c d w
         (rat_unit_coordinate j) i)"
  proof -
    show ?thesis
      apply (rule sum.cong)
       apply (rule refl)
    using brc_extended_x_from_y_minus_scale[
      where i = i
        and a = a and b = b and c = c and d = d
        and w = w]
      i_bound
      by simp
  qed

  show ?thesis
    using basis summed scaled
    by simp
qed

lemma brc_minus_coeff_xv1_representation:
  assumes v_form:
    "𝗏 = 4 * w - 1"
  assumes w_pos:
    "0 < w"
  shows
    "brc_xv1_from_y_minus a b c d w y
     =
     rat_linear_form (𝗏 + 1)
       (brc_minus_coeff a b c d w 𝗏)
       y"
proof -
  have expansion:
    "brc_extended_x_from_y_minus a b c d w y 𝗏
     =
     (∑j∈{0..<𝗏 + 1}.
        y j *
        brc_extended_x_from_y_minus a b c d w
          (rat_unit_coordinate j) 𝗏)"
    using brc_extended_x_from_y_minus_linear_expansion[
      where i = 𝗏
        and a = a and b = b and c = c and d = d
        and w = w and y = y,
      OF v_form w_pos]
    by simp

  have left:
    "brc_extended_x_from_y_minus a b c d w y 𝗏
     =
     brc_xv1_from_y_minus a b c d w y"
    unfolding brc_extended_x_from_y_minus_def
    by simp

  have right:
    "(∑j∈{0..<𝗏 + 1}.
       y j *
       brc_extended_x_from_y_minus a b c d w
         (rat_unit_coordinate j) 𝗏)
     =
     (∑j∈{0..<𝗏 + 1}.
       brc_minus_coeff a b c d w 𝗏 j *
       y j)"
  proof -
    show ?thesis
      apply (rule sum.cong)
       apply (rule refl)
    unfolding brc_extended_x_from_y_minus_def
      brc_minus_coeff_def
      by (simp add: mult.commute)
  qed

  show ?thesis
    unfolding rat_linear_form_def
    using expansion left right
    by simp
qed

lemma brc_minus_coeff_y0_representation:
  assumes v_form:
    "𝗏 = 4 * w - 1"
  assumes w_pos:
    "0 < w"
  shows
    "t_of
       (brc_x_from_y_minus a b c d w y)
     =
     rat_linear_form (𝗏 + 1)
       (brc_minus_coeff a b c d w (𝗏 + 1))
       y"
proof -
  let ?E =
    "brc_extended_x_from_y_minus a b c d w"

  have original:
    "brc_x_from_y_minus a b c d w y $$ (h,0)
     =
     ?E y h"
    if h_bound:
      "h < 𝗏"
    for h
    using h_bound
    unfolding brc_extended_x_from_y_minus_def
    by simp

  have entry:
    "?E y h
     =
     (∑j∈{0..<𝗏 + 1}.
        y j *
        ?E (rat_unit_coordinate j) h)"
    if h_bound:
      "h < 𝗏"
    for h
    using brc_extended_x_from_y_minus_linear_expansion[
      where i = h
        and a = a and b = b and c = c and d = d
        and w = w and y = y,
      OF v_form w_pos]
      h_bound
    by simp

  have expanded:
    "t_of
       (brc_x_from_y_minus a b c d w y)
     =
     (∑h∈{0..<𝗏}.
        ∑j∈{0..<𝗏 + 1}.
          y j *
          ?E (rat_unit_coordinate j) h)"
    unfolding t_of_def
    using original entry
    by (intro sum.cong) auto

  also have
    "... =
     (∑j∈{0..<𝗏 + 1}.
        ∑h∈{0..<𝗏}.
          y j *
          ?E (rat_unit_coordinate j) h)"
    by (rule sum.swap)

  also have
    "... =
     (∑j∈{0..<𝗏 + 1}.
        y j *
        (∑h∈{0..<𝗏}.
           ?E (rat_unit_coordinate j) h))"
  proof (rule sum.cong)
    show "{0..<𝗏 + 1} = {0..<𝗏 + 1}"
      by simp
  next
    fix j
    assume j_mem:
      "j ∈ {0..<𝗏 + 1}"

    show
      "(∑h∈{0..<𝗏}.
         y j * ?E (rat_unit_coordinate j) h)
       =
       y j *
       (∑h∈{0..<𝗏}.
          ?E (rat_unit_coordinate j) h)"
      by (metis sum_distrib_left)
  qed

  also have
    "... =
     (∑j∈{0..<𝗏 + 1}.
        y j *
        t_of
          (brc_x_from_y_minus a b c d w
            (rat_unit_coordinate j)))"
  proof -
    show ?thesis
      apply (rule sum.cong)
       apply (rule refl)
    unfolding t_of_def
      brc_extended_x_from_y_minus_def
      by simp
  qed

  also have
    "... =
     (∑j∈{0..<𝗏 + 1}.
        brc_minus_coeff a b c d w (𝗏 + 1) j *
        y j)"
    unfolding brc_minus_coeff_def
    by (intro sum.cong) (auto simp: mult.commute)

  also have
    "... =
     rat_linear_form (𝗏 + 1)
       (brc_minus_coeff a b c d w (𝗏 + 1))
       y"
    unfolding rat_linear_form_def
    by simp

  finally show ?thesis .
qed

lemma brc_minus_coeff_L_representation:
  assumes v_form:
    "𝗏 = 4 * w - 1"
  assumes w_pos:
    "0 < w"
  assumes r_bound:
    "r < 𝗏"
  shows
    "brc_L
       (brc_x_from_y_minus a b c d w y) r
     =
     rat_linear_form (𝗏 + 1)
       (brc_minus_coeff a b c d w r)
       y"
proof -
  let ?E =
    "brc_extended_x_from_y_minus a b c d w"

  have entry:
    "brc_x_from_y_minus a b c d w y $$ (h,0)
     =
     (∑j∈{0..<𝗏 + 1}.
        y j *
        ?E (rat_unit_coordinate j) h)"
    if h_mem:
      "h ∈ {0..<𝗏}"
    for h
  proof -
    have h_bound:
      "h < 𝗏"
      using h_mem
      by simp

    have original:
      "brc_x_from_y_minus a b c d w y $$ (h,0)
       =
       ?E y h"
      using h_bound
      unfolding brc_extended_x_from_y_minus_def
      by simp

    have expansion:
      "?E y h
       =
       (∑j∈{0..<𝗏 + 1}.
          y j *
          ?E (rat_unit_coordinate j) h)"
      using brc_extended_x_from_y_minus_linear_expansion[
        where i = h
          and a = a and b = b and c = c and d = d
          and w = w and y = y,
        OF v_form w_pos]
        h_bound
      by simp

    show ?thesis
      using original expansion
      by simp
  qed

  have expanded:
    "brc_L
       (brc_x_from_y_minus a b c d w y) r
     =
     (∑h∈{0..<𝗏}.
        of_int (N $$ (h,r)) *
        (∑j∈{0..<𝗏 + 1}.
           y j *
           ?E (rat_unit_coordinate j) h))"
    unfolding brc_L_def
    using entry
    by (intro sum.cong) auto

  also have
    "... =
     (∑h∈{0..<𝗏}.
        ∑j∈{0..<𝗏 + 1}.
          of_int (N $$ (h,r)) *
          (y j *
           ?E (rat_unit_coordinate j) h))"
  proof -
    show ?thesis
      apply (rule sum.cong)
       apply (rule refl)
      apply (simp only: sum_distrib_left)
      done
  qed

  also have
    "... =
     (∑j∈{0..<𝗏 + 1}.
        ∑h∈{0..<𝗏}.
          of_int (N $$ (h,r)) *
          (y j *
           ?E (rat_unit_coordinate j) h))"
    by (rule sum.swap)

  also have
    "... =
     (∑j∈{0..<𝗏 + 1}.
        y j *
        (∑h∈{0..<𝗏}.
           of_int (N $$ (h,r)) *
           ?E (rat_unit_coordinate j) h))"
  proof (rule sum.cong)
    show "{0..<𝗏 + 1} = {0..<𝗏 + 1}"
      by simp
  next
    fix j
    assume j_mem:
      "j ∈ {0..<𝗏 + 1}"

    show
      "(∑h∈{0..<𝗏}.
         of_int (N $$ (h,r)) *
         (y j * ?E (rat_unit_coordinate j) h))
       =
       y j *
       (∑h∈{0..<𝗏}.
          of_int (N $$ (h,r)) *
          ?E (rat_unit_coordinate j) h)"
      apply (simp only: sum_distrib_left)
      apply (rule sum.cong)
       apply (rule refl)
      apply (simp add:
          mult.assoc mult.left_commute mult.commute)
      done
  qed

  also have
    "... =
     (∑j∈{0..<𝗏 + 1}.
        y j *
        brc_L
          (brc_x_from_y_minus a b c d w
            (rat_unit_coordinate j)) r)"
  proof (rule sum.cong)
    show "{0..<𝗏 + 1} = {0..<𝗏 + 1}"
      by simp
  next
    fix j
    assume j_mem:
      "j ∈ {0..<𝗏 + 1}"

    have inner:
      "(∑h∈{0..<𝗏}.
         of_int (N $$ (h,r)) *
         ?E (rat_unit_coordinate j) h)
       =
       brc_L
         (brc_x_from_y_minus a b c d w
           (rat_unit_coordinate j)) r"
    proof -
      show ?thesis
        unfolding brc_L_def
      proof (rule sum.cong)
        show "{0..<𝗏} = {0..<𝗏}"
          by simp
      next
        fix h
        assume h_mem:
          "h ∈ {0..<𝗏}"

        have h_bound:
          "h < 𝗏"
          using h_mem
          by simp

        have coordinate:
          "?E (rat_unit_coordinate j) h
           =
           brc_x_from_y_minus a b c d w
             (rat_unit_coordinate j) $$ (h,0)"
          using h_bound
          unfolding brc_extended_x_from_y_minus_def
          by simp

        show
          "of_int (N $$ (h,r)) *
             ?E (rat_unit_coordinate j) h
           =
           of_int (N $$ (h,r)) *
             brc_x_from_y_minus a b c d w
               (rat_unit_coordinate j) $$ (h,0)"
          using coordinate
          by simp
      qed
    qed

    show
      "y j *
       (∑h∈{0..<𝗏}.
          of_int (N $$ (h,r)) *
          ?E (rat_unit_coordinate j) h)
       =
       y j *
       brc_L
         (brc_x_from_y_minus a b c d w
           (rat_unit_coordinate j)) r"
      using inner
      by simp
  qed

  also have
    "... =
     (∑j∈{0..<𝗏 + 1}.
        brc_minus_coeff a b c d w r j *
        y j)"
    using r_bound
    unfolding brc_minus_coeff_def
    by (intro sum.cong) (auto simp: mult.commute)

  also have
    "... =
     rat_linear_form (𝗏 + 1)
       (brc_minus_coeff a b c d w r)
       y"
    unfolding rat_linear_form_def
    by simp

  finally show ?thesis .
qed

definition brc_extended_matrix_from_y_minus ::
  "nat ⇒ nat ⇒ nat ⇒ nat ⇒ nat ⇒
   (nat ⇒ rat) ⇒ rat mat" where
  "brc_extended_matrix_from_y_minus a b c d w y =
     mat (𝗏 + 1) 1
       (λ(i,j).
          if j ≠ 0 then 0
          else
            brc_inverse_y_block
              a b c d y
              (i div 4) (i mod 4))"

lemma brc_extended_matrix_minus_block:
  assumes v_form:
    "𝗏 = 4 * w - 1"
  assumes w_pos:
    "0 < w"
  assumes h_lt:
    "h < w"
  assumes j_lt:
    "j < 4"
  shows
    "brc_extended_matrix_from_y_minus
       a b c d w y $$ (4*h+j,0)
     =
     brc_inverse_y_block a b c d y h j"
proof -
  have index_lt:
    "4*h+j < 𝗏 + 1"
    using v_form w_pos h_lt j_lt
    by simp

  have div:
    "(4*h+j) div 4 = h"
    using j_lt
    by simp

  have mod:
    "(4*h+j) mod 4 = j"
    using j_lt
    by simp

  show ?thesis
    unfolding brc_extended_matrix_from_y_minus_def
    using index_lt div mod
    by simp
qed

lemma brc_extended_matrix_minus_block_sqsum:
  assumes v_form:
    "𝗏 = 4 * w - 1"
  assumes w_pos:
    "0 < w"
  assumes h_lt:
    "h < w"
  assumes nz:
    "a^2 + b^2 + c^2 + d^2 ≠ 0"
  shows
    "y_block_sqsum a b c d
       (brc_extended_matrix_from_y_minus
         a b c d w y) h
     =
     (y (4*h))^2 +
     (y (4*h+1))^2 +
     (y (4*h+2))^2 +
     (y (4*h+3))^2"
proof -
  let ?X =
    "brc_extended_matrix_from_y_minus
      a b c d w y"

  have x0:
    "?X $$ (4*h,0)
     =
     brc_inverse_y_block a b c d y h 0"
    using brc_extended_matrix_minus_block[
      where w = w and h = h and j = 0
        and a = a and b = b and c = c and d = d
        and y = y,
      OF v_form w_pos h_lt]
    by simp

  have x1:
    "?X $$ (4*h+1,0)
     =
     brc_inverse_y_block a b c d y h 1"
    using brc_extended_matrix_minus_block[
      where w = w and h = h and j = 1
        and a = a and b = b and c = c and d = d
        and y = y,
      OF v_form w_pos h_lt]
    by simp

  have x2:
    "?X $$ (4*h+2,0)
     =
     brc_inverse_y_block a b c d y h 2"
    using brc_extended_matrix_minus_block[
      where w = w and h = h and j = 2
        and a = a and b = b and c = c and d = d
        and y = y,
      OF v_form w_pos h_lt]
    by simp

  have x3:
    "?X $$ (4*h+3,0)
     =
     brc_inverse_y_block a b c d y h 3"
    using brc_extended_matrix_minus_block[
      where w = w and h = h and j = 3
        and a = a and b = b and c = c and d = d
        and y = y,
      OF v_form w_pos h_lt]
    by simp

  have forward:
    "y_of
      ((a,b,c,d),
       (?X $$ (4*h,0),
        ?X $$ (4*h+1,0),
        ?X $$ (4*h+2,0),
        ?X $$ (4*h+3,0)))
     =
     (y (4*h), y (4*h+1),
      y (4*h+2), y (4*h+3))"
    using brc_inverse_y_block_forward[
      where a = a and b = b and c = c and d = d
        and y = y and h = h,
      OF nz]
      x0 x1 x2 x3
    by simp

  show ?thesis
    unfolding y_block_sqsum_def
    using forward
    by simp
qed

lemma brc_extended_matrix_minus_eq_extend:
  assumes v_form:
    "𝗏 = 4 * w - 1"
  assumes w_pos:
    "0 < w"
  assumes i_bound:
    "i < 𝗏 + 1"
  shows
    "brc_extended_matrix_from_y_minus
       a b c d w y $$ (i,0)
     =
     brc_extend_x
       (brc_x_from_y_minus a b c d w y)
       (brc_xv1_from_y_minus a b c d w y)
       $$ (i,0)"
proof (cases "i < 𝗏")
  case True

  have left:
    "brc_extended_matrix_from_y_minus
       a b c d w y $$ (i,0)
     =
     brc_inverse_y_block
       a b c d y (i div 4) (i mod 4)"
    unfolding brc_extended_matrix_from_y_minus_def
    using i_bound
    by simp

  have right:
    "brc_x_from_y_minus a b c d w y $$ (i,0)
     =
     brc_inverse_y_block
       a b c d y (i div 4) (i mod 4)"
    unfolding brc_x_from_y_minus_def
    using True
    by simp

  show ?thesis
    unfolding brc_extend_x_def
    using True left right
    by simp
next
  case False

  have i_eq:
    "i = 𝗏"
    using i_bound False
    by simp

  have left:
    "brc_extended_matrix_from_y_minus
       a b c d w y $$ (𝗏,0)
     =
     brc_xv1_from_y_minus a b c d w y"
    unfolding brc_extended_matrix_from_y_minus_def
      brc_xv1_from_y_minus_def
    using v_form w_pos
    by simp

  show ?thesis
    unfolding brc_extend_x_def
    using i_eq left
    by simp
qed

lemma brc_extended_matrix_minus_blocks_sqsum:
  assumes v_form:
    "𝗏 = 4 * w - 1"
  assumes w_pos:
    "0 < w"
  assumes nz:
    "a^2 + b^2 + c^2 + d^2 ≠ 0"
  shows
    "y_blocks_sqsum a b c d
       (brc_extended_matrix_from_y_minus
         a b c d w y) w
     =
     (∑i∈{0..<𝗏 + 1}. (y i)^2)"
proof -
  have blocks:
    "y_blocks_sqsum a b c d
       (brc_extended_matrix_from_y_minus
         a b c d w y) w
     =
     (∑h∈{0..<w}.
        ((y (4*h))^2 +
         (y (4*h+1))^2 +
         (y (4*h+2))^2 +
         (y (4*h+3))^2))"
  proof -
    show ?thesis
      unfolding y_blocks_sqsum_def
      apply (rule sum.cong)
       apply (rule refl)
    using brc_extended_matrix_minus_block_sqsum[
      where w = w and a = a and b = b
        and c = c and d = d and y = y,
      OF v_form w_pos _ nz]
      by auto
  qed

  have regroup:
    "(∑i∈{0..<4*w}. (y i)^2)
     =
     (∑h∈{0..<w}.
        ((y (4*h))^2 +
         (y (4*h+1))^2 +
         (y (4*h+2))^2 +
         (y (4*h+3))^2))"
    using sum_four_blocks[
      where w = w and f = "λi. (y i)^2"]
    .

  have range:
    "𝗏 + 1 = 4*w"
    using v_form w_pos
    by simp

  show ?thesis
    using blocks regroup range
    by simp
qed

lemma brc_minus_weighted_initial:
  assumes v_form:
    "𝗏 = 4 * w - 1"
  assumes w_pos:
    "0 < w"
  assumes abcd:
    "𝗄 - Λ = a^2 + b^2 + c^2 + d^2"
  shows
    "⋀y.
       rat_weighted_linear_squares_from
         (𝗏 + 1) 0 (𝗏 + 2)
         brc_minus_weight
         (brc_minus_coeff a b c d w)
         y
       =
       rat_diagonal_form
         (𝗏 + 1) brc_minus_diagonal y"
proof -
  fix y

  let ?x =
    "brc_x_from_y_minus a b c d w y"

  let ?xv1 =
    "brc_xv1_from_y_minus a b c d w y"

  have diff_nz:
    "𝗄 - Λ ≠ 0"
    using blocksize_gt_index
    by simp

  have nz:
    "a^2 + b^2 + c^2 + d^2 ≠ 0"
    using abcd diff_nz
    by metis

  have transformed:
    "(∑r∈{0..<𝗏}. (brc_L ?x r)^2)
       + of_nat (𝗄 - Λ) * ?xv1^2
     =
       of_nat Λ * (t_of ?x)^2
       +
       (∑h∈{0..<w}.
          y_block_sqsum a b c d
            (brc_extend_x ?x ?xv1) h)"
    using brc_x_equation_minus_transformed[
      OF v_form w_pos abcd,
      of ?x ?xv1]
    unfolding brc_L_def t_of_def
    by simp

  have block_entries:
    "brc_extend_x ?x ?xv1 $$ (i,0)
     =
     brc_extended_matrix_from_y_minus
       a b c d w y $$ (i,0)"
    if i_bound:
      "i < 𝗏 + 1"
    for i
    using brc_extended_matrix_minus_eq_extend[
      where i = i
        and w = w and a = a and b = b
        and c = c and d = d and y = y,
      OF v_form w_pos i_bound]
    by simp

  have blocks:
    "(∑h∈{0..<w}.
       y_block_sqsum a b c d
         (brc_extend_x ?x ?xv1) h)
     =
     (∑i∈{0..<𝗏 + 1}. (y i)^2)"
  proof -
    have block_eq:
      "y_block_sqsum a b c d
         (brc_extend_x ?x ?xv1) h
       =
       y_block_sqsum a b c d
         (brc_extended_matrix_from_y_minus
           a b c d w y) h"
      if h_mem:
        "h ∈ {0..<w}"
      for h
    proof -
      have h_lt:
        "h < w"
        using h_mem
        by simp

      have e0:
        "brc_extend_x ?x ?xv1 $$ (4*h,0)
         =
         brc_extended_matrix_from_y_minus
           a b c d w y $$ (4*h,0)"
        using block_entries h_lt v_form w_pos
        by simp

      have e1:
        "brc_extend_x ?x ?xv1 $$ (4*h+1,0)
         =
         brc_extended_matrix_from_y_minus
           a b c d w y $$ (4*h+1,0)"
        using block_entries h_lt v_form w_pos
        by simp

      have e2:
        "brc_extend_x ?x ?xv1 $$ (4*h+2,0)
         =
         brc_extended_matrix_from_y_minus
           a b c d w y $$ (4*h+2,0)"
        using block_entries h_lt v_form w_pos
        by simp

      have e3:
        "brc_extend_x ?x ?xv1 $$ (4*h+3,0)
         =
         brc_extended_matrix_from_y_minus
           a b c d w y $$ (4*h+3,0)"
        using block_entries h_lt v_form w_pos
        by simp

      show ?thesis
        unfolding y_block_sqsum_def
        using e0 e1 e2 e3
        by simp
    qed

    have sum_eq:
      "(∑h∈{0..<w}.
         y_block_sqsum a b c d
           (brc_extend_x ?x ?xv1) h)
       =
       y_blocks_sqsum a b c d
         (brc_extended_matrix_from_y_minus
           a b c d w y) w"
      unfolding y_blocks_sqsum_def
      using block_eq
      by (intro sum.cong) auto

    show ?thesis
      using sum_eq
        brc_extended_matrix_minus_blocks_sqsum[
          where w = w and a = a and b = b
            and c = c and d = d and y = y,
          OF v_form w_pos nz]
      by simp
  qed

  have L_forms:
    "(∑r∈{0..<𝗏}.
       (rat_linear_form (𝗏 + 1)
          (brc_minus_coeff a b c d w r) y)^2)
     =
     (∑r∈{0..<𝗏}. (brc_L ?x r)^2)"
  proof -
    show ?thesis
      apply (rule sum.cong)
       apply (rule refl)
    using brc_minus_coeff_L_representation[
      where w = w and a = a and b = b
        and c = c and d = d and y = y,
      OF v_form w_pos]
      by auto
  qed

  have xv1_form:
    "rat_linear_form (𝗏 + 1)
       (brc_minus_coeff a b c d w 𝗏) y
     =
     ?xv1"
    using brc_minus_coeff_xv1_representation[
      where w = w and a = a and b = b
        and c = c and d = d and y = y,
      OF v_form w_pos]
    by simp

  have y0_form:
    "rat_linear_form (𝗏 + 1)
       (brc_minus_coeff a b c d w (𝗏 + 1)) y
     =
     t_of ?x"
    using brc_minus_coeff_y0_representation[
      where w = w and a = a and b = b
        and c = c and d = d and y = y,
      OF v_form w_pos]
    by simp

  have weighted:
    "rat_weighted_linear_squares_from
       (𝗏 + 1) 0 (𝗏 + 2)
       brc_minus_weight
       (brc_minus_coeff a b c d w) y
     =
     (∑r∈{0..<𝗏}. (brc_L ?x r)^2)
       + of_nat (𝗄 - Λ) * ?xv1^2
       - of_nat Λ * (t_of ?x)^2"
  proof -
    show ?thesis
      unfolding rat_weighted_linear_squares_from_def
        brc_minus_weight_def
      using L_forms xv1_form y0_form
      by (simp add: sum.atLeastLessThan_Suc)
  qed

  have diagonal:
    "rat_diagonal_form
       (𝗏 + 1) brc_minus_diagonal y
     =
     (∑i∈{0..<𝗏 + 1}. (y i)^2)"
    unfolding rat_diagonal_form_def
      brc_minus_diagonal_def
    by simp

  have rearranged:
    "(∑r∈{0..<𝗏}. (brc_L ?x r)^2)
       + of_nat (𝗄 - Λ) * ?xv1^2
       - of_nat Λ * (t_of ?x)^2
     =
     (∑i∈{0..<𝗏 + 1}. (y i)^2)"
    using transformed blocks
    by simp

  show
    "rat_weighted_linear_squares_from
       (𝗏 + 1) 0 (𝗏 + 2)
       brc_minus_weight
       (brc_minus_coeff a b c d w) y
     =
     rat_diagonal_form
       (𝗏 + 1) brc_minus_diagonal y"
    using weighted diagonal rearranged
    by simp
qed

lemma brc_minus_rational_solution:
  assumes v_form:
    "𝗏 = 4 * w - 1"
  assumes w_pos:
    "0 < w"
  assumes abcd:
    "𝗄 - Λ = a^2 + b^2 + c^2 + d^2"
  shows
    "∃x y z :: rat.
       (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧
       x^2 =
         of_nat (𝗄 - Λ) * y^2
         - of_nat Λ * z^2"
proof -
  have n_pos:
    "0 < 𝗏 + 1"
    by simp

  have elimination_weights:
    "⋀q. q < (𝗏 + 1) - 1 ⟹
       brc_minus_weight q = 1"
  proof -
    fix q
    assume q_lt:
      "q < (𝗏 + 1) - 1"

    have "q < 𝗏"
      using q_lt
      by simp

    then show
      "brc_minus_weight q = 1"
      using brc_minus_weight_L
      by blast
  qed

  have first_terminal:
    "brc_minus_weight ((𝗏 + 1) - 1)
     =
     of_nat (𝗄 - Λ)"
    using brc_minus_weight_xv1
    by simp

  have second_terminal:
    "brc_minus_weight (𝗏 + 1)
     =
     - of_nat Λ"
    using brc_minus_weight_y0 .

  have diagonal_units:
    "⋀q. q < (𝗏 + 1) - 1 ⟹
       brc_minus_diagonal q = 1"
    using brc_minus_diagonal_one
    by blast

  have diagonal_last:
    "brc_minus_diagonal ((𝗏 + 1) - 1) = 1"
    using brc_minus_diagonal_one .

  have initial:
    "⋀u.
       rat_weighted_linear_squares_from
         (𝗏 + 1) 0 ((𝗏 + 1) + 1)
         brc_minus_weight
         (brc_minus_coeff a b c d w)
         u
       =
       rat_diagonal_form
         (𝗏 + 1) brc_minus_diagonal u"
    using brc_minus_weighted_initial[
      OF v_form w_pos abcd]
    by simp

  show ?thesis
    using rat_weighted_elimination_terminal_solution_general[
      where n = "𝗏 + 1"
        and C = "brc_minus_coeff a b c d w"
        and d = brc_minus_diagonal
        and W = brc_minus_weight
        and alpha = "of_nat (𝗄 - Λ)"
        and beta = "- of_nat Λ",
      OF n_pos elimination_weights
         first_terminal second_terminal
         diagonal_units diagonal_last initial]
    by simp
qed

lemma brc_plus_rational_solution_exists:
  assumes v_form:
    "𝗏 = 4 * w + 1"
  shows
    "∃x y z :: rat.
       (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧
       x^2 =
         of_nat (𝗄 - Λ) * y^2 +
         of_nat Λ * z^2"
proof -
  obtain a b c d :: nat where abcd:
    "𝗄 - Λ = a^2 + b^2 + c^2 + d^2"
    using sum_of_four_squares[
      of "𝗄 - Λ"]
    by blast

  show ?thesis
    using brc_plus_rational_solution[
      OF v_form abcd]
    .
qed

lemma brc_minus_rational_solution_exists:
  assumes v_form:
    "𝗏 = 4 * w - 1"
  assumes w_pos:
    "0 < w"
  shows
    "∃x y z :: rat.
       (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧
       x^2 =
         of_nat (𝗄 - Λ) * y^2
         - of_nat Λ * z^2"
proof -
  obtain a b c d :: nat where abcd:
    "𝗄 - Λ = a^2 + b^2 + c^2 + d^2"
    using sum_of_four_squares[
      of "𝗄 - Λ"]
    by blast

  show ?thesis
    using brc_minus_rational_solution[
      OF v_form w_pos abcd]
    .
qed

lemma brc_v_eq_4w_minus_1:
  assumes mod3:
    "𝗏 mod 4 = 3"
  shows
    "∃w. 0 < w ∧ 𝗏 = 4 * w - 1"
proof -
  let ?q = "𝗏 div 4"
  let ?w = "Suc ?q"

  have division:
    "𝗏 = 4 * ?q + 3"
  proof -
    have
      "𝗏 div 4 * 4 + 𝗏 mod 4 = 𝗏"
      using div_mult_mod_eq[
        of 𝗏 4]
      by simp

    then show ?thesis
      using mod3
      by (simp add: mult.commute)
  qed

  have w_pos:
    "0 < ?w"
    by simp

  have form:
    "𝗏 = 4 * ?w - 1"
    using division
    by simp

  show ?thesis
    using w_pos form
    by blast
qed

lemma rat_as_int_quotient:
  fixes r :: rat
  obtains n d :: int where
    "d ≠ 0"
    "r = of_int n / of_int d"
proof -
  obtain n d :: int where q:
    "quotient_of r = (n,d)"
    by (cases "quotient_of r") auto

  have d_pos:
    "0 < d"
    using Rat.quotient_of_denom_pos[
      OF q]
    .

  have d_nz:
    "d ≠ 0"
    using d_pos
    by simp

  have representation:
    "r = of_int n / of_int d"
    using Rat.quotient_of_div[
      OF q]
    .

  show thesis
    using that[OF d_nz representation]
    .
qed

lemma rat_quadratic_solution_to_int:
  fixes A B :: int
  fixes x y z :: rat
  assumes nonzero:
    "x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0"
  assumes equation:
    "x^2 =
       of_int A * y^2 +
       of_int B * z^2"
  shows
    "∃X Y Z :: int.
       (X ≠ 0 ∨ Y ≠ 0 ∨ Z ≠ 0) ∧
       X^2 = A * Y^2 + B * Z^2"
proof -
  obtain nx dx :: int where
    dx_nz: "dx ≠ 0"
    and x_rep:
      "x = of_int nx / of_int dx"
    using rat_as_int_quotient[of x]
    by blast

  obtain ny dy :: int where
    dy_nz: "dy ≠ 0"
    and y_rep:
      "y = of_int ny / of_int dy"
    using rat_as_int_quotient[of y]
    by blast

  obtain nz dz :: int where
    dz_nz: "dz ≠ 0"
    and z_rep:
      "z = of_int nz / of_int dz"
    using rat_as_int_quotient[of z]
    by blast

  let ?D = "dx * dy * dz"
  let ?X = "nx * dy * dz"
  let ?Y = "ny * dx * dz"
  let ?Z = "nz * dx * dy"

  have D_nz:
    "?D ≠ 0"
    using dx_nz dy_nz dz_nz
    by simp

  have D_rat_nz:
    "(of_int ?D :: rat) ≠ 0"
    using D_nz
    by simp

  have scale_x:
    "(of_int ?D :: rat) * x = of_int ?X"
    unfolding x_rep
    using dx_nz
    by simp

  have scale_y:
    "(of_int ?D :: rat) * y = of_int ?Y"
    unfolding y_rep
    using dy_nz
    by simp

  have scale_z:
    "(of_int ?D :: rat) * z = of_int ?Z"
    unfolding z_rep
    using dz_nz
    by simp

  have scaled_equation:
    "((of_int ?D :: rat) * x)^2
     =
     of_int A * ((of_int ?D :: rat) * y)^2
     +
     of_int B * ((of_int ?D :: rat) * z)^2"
  proof -
    have
      "((of_int ?D :: rat) * x)^2
       =
       (of_int ?D :: rat)^2 * x^2"
      by (simp add: power2_eq_square)

    also have
      "... =
       (of_int ?D :: rat)^2 *
       (of_int A * y^2 + of_int B * z^2)"
      using equation
      by simp

    also have
      "... =
       of_int A * ((of_int ?D :: rat) * y)^2
       +
       of_int B * ((of_int ?D :: rat) * z)^2"
      by (simp add:
          power2_eq_square algebra_simps)

    finally show ?thesis .
  qed

  have scale_x_sq:
    "((of_int ?D :: rat) * x)^2
     =
     (of_int ?X :: rat)^2"
    using scale_x
    by (rule arg_cong[
      where f = "λt::rat. t^2"])

  have scale_y_sq:
    "((of_int ?D :: rat) * y)^2
     =
     (of_int ?Y :: rat)^2"
    using scale_y
    by (rule arg_cong[
      where f = "λt::rat. t^2"])

  have scale_z_sq:
    "((of_int ?D :: rat) * z)^2
     =
     (of_int ?Z :: rat)^2"
    using scale_z
    by (rule arg_cong[
      where f = "λt::rat. t^2"])

  have rat_equation:
    "(of_int ?X :: rat)^2
     =
     of_int A * (of_int ?Y :: rat)^2
     +
     of_int B * (of_int ?Z :: rat)^2"
  proof -
    have
      "(of_int ?X :: rat)^2
       =
       ((of_int ?D :: rat) * x)^2"
      using scale_x_sq
      by simp

    also have
      "... =
       of_int A * ((of_int ?D :: rat) * y)^2
       +
       of_int B * ((of_int ?D :: rat) * z)^2"
      using scaled_equation
      .

    also have
      "... =
       of_int A * (of_int ?Y :: rat)^2
       +
       of_int B * (of_int ?Z :: rat)^2"
      using scale_y_sq scale_z_sq
      by (simp only:)

    finally show ?thesis .
  qed

  have cast_equation:
    "(of_int (?X^2) :: rat)
     =
     of_int (A * ?Y^2 + B * ?Z^2)"
    using rat_equation
    by simp

  have int_equation:
    "?X^2 = A * ?Y^2 + B * ?Z^2"
    using cast_equation
    by (metis of_int_eq_iff)

  have scaled_nonzero:
    "(of_int ?D :: rat) * x ≠ 0 ∨
     (of_int ?D :: rat) * y ≠ 0 ∨
     (of_int ?D :: rat) * z ≠ 0"
  proof -
    from nonzero show ?thesis
    proof
      assume x_nz:
        "x ≠ 0"

      have
        "(of_int ?D :: rat) * x ≠ 0"
        using D_rat_nz x_nz
        by simp

      then show ?thesis
        by blast
    next
      assume yz_nz:
        "y ≠ 0 ∨ z ≠ 0"

      from yz_nz show ?thesis
      proof
        assume y_nz:
          "y ≠ 0"

        have
          "(of_int ?D :: rat) * y ≠ 0"
          using D_rat_nz y_nz
          by simp

        then show ?thesis
          by blast
      next
        assume z_nz:
          "z ≠ 0"

        have
          "(of_int ?D :: rat) * z ≠ 0"
          using D_rat_nz z_nz
          by simp

        then show ?thesis
          by blast
      qed
    qed
  qed

  have int_nonzero:
    "?X ≠ 0 ∨ ?Y ≠ 0 ∨ ?Z ≠ 0"
  proof -
    from scaled_nonzero show ?thesis
    proof
      assume x_scaled_nz:
        "(of_int ?D :: rat) * x ≠ 0"

      have X_nz:
        "?X ≠ 0"
      proof
        assume X_zero:
          "?X = 0"

        have
          "(of_int ?D :: rat) * x = 0"
          using scale_x X_zero
          by simp

        then show False
          using x_scaled_nz
          by contradiction
      qed

      show ?thesis
        using X_nz
        by blast
    next
      assume yz_scaled_nz:
        "(of_int ?D :: rat) * y ≠ 0 ∨
         (of_int ?D :: rat) * z ≠ 0"

      from yz_scaled_nz show ?thesis
      proof
        assume y_scaled_nz:
          "(of_int ?D :: rat) * y ≠ 0"

        have Y_nz:
          "?Y ≠ 0"
        proof
          assume Y_zero:
            "?Y = 0"

          have
            "(of_int ?D :: rat) * y = 0"
            using scale_y Y_zero
            by simp

          then show False
            using y_scaled_nz
            by contradiction
        qed

        show ?thesis
          using Y_nz
          by blast
      next
        assume z_scaled_nz:
          "(of_int ?D :: rat) * z ≠ 0"

        have Z_nz:
          "?Z ≠ 0"
        proof
          assume Z_zero:
            "?Z = 0"

          have
            "(of_int ?D :: rat) * z = 0"
            using scale_z Z_zero
            by simp

          then show False
            using z_scaled_nz
            by contradiction
        qed

        show ?thesis
          using Z_nz
          by blast
      qed
    qed
  qed

  show ?thesis
    using int_nonzero int_equation
    by blast
qed

lemma brc_sign_plus:
  assumes v_form:
    "𝗏 = 4 * w + 1"
  shows
    "(-1::int)^((𝗏 - 1) div 2) = 1"
proof -
  have exponent:
    "(𝗏 - 1) div 2 = 2*w"
    using v_form
    by simp

  show ?thesis
    unfolding exponent
    by (simp add: power_mult)
qed

lemma brc_sign_minus:
  assumes v_form:
    "𝗏 = 4 * w - 1"
  assumes w_pos:
    "0 < w"
  shows
    "(-1::int)^((𝗏 - 1) div 2) = -1"
proof -
  obtain s where w_eq:
    "w = Suc s"
    using w_pos
    by (cases w) auto

  have v_eq:
    "𝗏 = 4*s + 3"
    using v_form w_eq
    by simp

  have exponent:
    "(𝗏 - 1) div 2 = 2*s + 1"
    using v_eq
    by simp

  show ?thesis
    unfolding exponent
    by (simp add: power_add power_mult)
qed

lemma brc_plus_integer_solution_exists:
  assumes v_form:
    "𝗏 = 4 * w + 1"
  shows
    "∃x y z :: int.
       (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧
       x^2 =
         int (𝗄 - Λ) * y^2 +
         int Λ * z^2"
proof -
  obtain x y z :: rat where nz:
    "x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0"
    and eq:
    "x^2 =
       of_nat (𝗄 - Λ) * y^2 +
       of_nat Λ * z^2"
    using brc_plus_rational_solution_exists[
      OF v_form]
    by blast

  have eq_cast:
    "x^2 =
       of_int (int (𝗄 - Λ)) * y^2 +
       of_int (int Λ) * z^2"
    using eq
    by simp

  show ?thesis
    using rat_quadratic_solution_to_int[
      where A = "int (𝗄 - Λ)"
        and B = "int Λ"
        and x = x and y = y and z = z,
      OF nz eq_cast]
    .
qed

lemma brc_minus_integer_solution_exists:
  assumes v_form:
    "𝗏 = 4 * w - 1"
  assumes w_pos:
    "0 < w"
  shows
    "∃x y z :: int.
       (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧
       x^2 =
         int (𝗄 - Λ) * y^2 -
         int Λ * z^2"
proof -
  obtain x y z :: rat where nz:
    "x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0"
    and eq:
    "x^2 =
       of_nat (𝗄 - Λ) * y^2 -
       of_nat Λ * z^2"
    using brc_minus_rational_solution_exists[
      OF v_form w_pos]
    by blast

  have eq_cast:
    "x^2 =
       of_int (int (𝗄 - Λ)) * y^2 +
       of_int (- int Λ) * z^2"
    using eq
    by simp

  obtain X Y Z :: int where nz_int:
    "X ≠ 0 ∨ Y ≠ 0 ∨ Z ≠ 0"
    and eq_int:
    "X^2 =
       int (𝗄 - Λ) * Y^2 +
       (- int Λ) * Z^2"
    using rat_quadratic_solution_to_int[
      where A = "int (𝗄 - Λ)"
        and B = "- int Λ"
        and x = x and y = y and z = z,
      OF nz eq_cast]
    by blast

  have eq_minus:
    "X^2 =
       int (𝗄 - Λ) * Y^2 -
       int Λ * Z^2"
    using eq_int
    by simp

  show ?thesis
    using nz_int eq_minus
    by blast
qed

theorem bruck_ryser_chowla_odd:
  assumes odd_v:
    "odd 𝗏"
  shows
    "∃x y z :: int.
       (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧
       x^2 =
         int (𝗄 - Λ) * y^2 +
         (-1::int)^((𝗏 - 1) div 2) *
         int Λ * z^2"
proof -
  have mod_cases:
    "𝗏 mod 4 = 1 ∨ 𝗏 mod 4 = 3"
    using odd_mod_four_cases[
      OF odd_v]
    .

  from mod_cases show ?thesis
  proof
    assume mod1:
      "𝗏 mod 4 = 1"

    obtain w where v_form:
      "𝗏 = 4 * w + 1"
      using brc_v_eq_4w_plus_1[
        OF mod1]
      by blast

    obtain x y z :: int where nz:
      "x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0"
      and eq:
      "x^2 =
       int (𝗄 - Λ) * y^2 +
       int Λ * z^2"
      using brc_plus_integer_solution_exists[
        OF v_form]
      by blast

    have sign:
      "(-1::int)^((𝗏 - 1) div 2) = 1"
      using brc_sign_plus[
        OF v_form]
      .

    have signed_eq:
      "x^2 =
       int (𝗄 - Λ) * y^2 +
       (-1::int)^((𝗏 - 1) div 2) *
       int Λ * z^2"
      using eq sign
      by simp

    show ?thesis
      using nz signed_eq
      by blast
  next
    assume mod3:
      "𝗏 mod 4 = 3"

    obtain w where w_pos:
      "0 < w"
      and v_form:
      "𝗏 = 4 * w - 1"
      using brc_v_eq_4w_minus_1[
        OF mod3]
      by blast

    obtain x y z :: int where nz:
      "x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0"
      and eq:
      "x^2 =
       int (𝗄 - Λ) * y^2 -
       int Λ * z^2"
      using brc_minus_integer_solution_exists[
        OF v_form w_pos]
      by blast

    have sign:
      "(-1::int)^((𝗏 - 1) div 2) = -1"
      using brc_sign_minus[
        OF v_form w_pos]
      .

    have signed_eq:
      "x^2 =
       int (𝗄 - Λ) * y^2 +
       (-1::int)^((𝗏 - 1) div 2) *
       int Λ * z^2"
      using eq sign
      by simp

    show ?thesis
      using nz signed_eq
      by blast
  qed
qed

end
end
