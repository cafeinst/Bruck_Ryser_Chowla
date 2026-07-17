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
      (q0 ≠ 0 ∨ q1 ≠ 0 ∨ q2 ≠ 0) ∧
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

lemma y_first_block_identity:
  fixes a b c d :: nat
  fixes x :: "rat mat"
  assumes abcd: "𝗄 - Λ = a^2 + b^2 + c^2 + d^2"
  shows
    "of_nat (𝗄 - Λ) *
      ((x $$ (0,0))^2 + (x $$ (1,0))^2 + (x $$ (2,0))^2 + (x $$ (3,0))^2)
     =
     (one_of (y_of ((a,b,c,d),
        (x $$ (0,0), x $$ (1,0), x $$ (2,0), x $$ (3,0)))))^2 +
     (two_of (y_of ((a,b,c,d),
        (x $$ (0,0), x $$ (1,0), x $$ (2,0), x $$ (3,0)))))^2 +
     (three_of (y_of ((a,b,c,d),
        (x $$ (0,0), x $$ (1,0), x $$ (2,0), x $$ (3,0)))))^2 +
     (four_of (y_of ((a,b,c,d),
        (x $$ (0,0), x $$ (1,0), x $$ (2,0), x $$ (3,0)))))^2"
  using y_block_sum_identity[OF abcd,
      of "x $$ (0,0)" "x $$ (1,0)" "x $$ (2,0)" "x $$ (3,0)"]
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

lemma y_block_4h_1:
  "y_block a b c d x (4*h + 1) =
   two_of (y_of ((a,b,c,d),
     (x $$ (4*h,0), x $$ (4*h + 1,0),
      x $$ (4*h + 2,0), x $$ (4*h + 3,0))))"
proof -
  have div_eq: "Suc (4*h) div 4 = h"
    by simp
  have mod_eq: "Suc (4*h) mod 4 = 1"
    by simp
  show ?thesis
    unfolding y_block_def Let_def
    using div_eq mod_eq
    by simp
qed

lemma y_block_4h_3:
  "y_block a b c d x (4*h + 3) =
   four_of (y_of ((a,b,c,d),
     (x $$ (4*h,0), x $$ (4*h + 1,0),
      x $$ (4*h + 2,0), x $$ (4*h + 3,0))))"
  unfolding y_block_def
  by simp

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

definition transformed_identity where
  "transformed_identity a b c d x w ≡
   (∑i∈{0..<𝗏}.
      (∑h∈{0..<𝗏}. of_int (N $$ (h,i)) * x $$ (h,0))^2)
    =
    of_nat Λ * (x_head_sum x w + x_last x w)^2
    +
    y_blocks_sqsum a b c d x w
    +
    of_nat (𝗄 - Λ) * (x_last x w)^2"

lemma transformed_identity_exists:
  assumes v_form: "𝗏 = 4 * w + 1"
  assumes abcd: "𝗄 - Λ = a^2 + b^2 + c^2 + d^2"
  assumes head_blocks:
    "x_head_sqsum x w = (∑h∈{0..<w}. x_block_sqsum x h)"
  shows "transformed_identity a b c d x w"
  using brc_x_equation_transformed_conditional[
      OF v_form abcd head_blocks]
  unfolding transformed_identity_def
  by simp

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

lemma choose_y_square_cancel:
  fixes e rest :: rat
  shows "∃y :: rat. (e * y + rest)^2 = y^2"
proof (cases "e = 1")
  case True
  have "(e * (-rest/2) + rest)^2 = (-rest/2)^2"
    using True
    by (simp add: power2_eq_square algebra_simps)
  thus ?thesis
    by blast
next
  case False
  let ?y = "rest / (1 - e)"

  have nz: "1 - e ≠ 0"
    using False by simp

  have lhs:
    "e * ?y + rest = ?y"
  proof -
    have "e * (rest/(1-e)) + rest
        = (e*rest + rest*(1-e)) / (1-e)"
      using nz
      by (simp add: divide_simps)
    also have "... = rest/(1-e)"
      by (simp add: algebra_simps)
    finally show ?thesis
      by simp
  qed

  have "(e * ?y + rest)^2 = ?y^2"
    using lhs by simp
  thus ?thesis
    by blast
qed

lemma eliminate_one_square_from_equation:
  fixes e rest RHS :: rat
  assumes eq: "(e * y + rest)^2 + T = y^2 + RHS"
  assumes cancel: "(e * y + rest)^2 = y^2"
  shows "T = RHS"
  using eq cancel
  by simp

lemma eliminate_square_from_sum:
  fixes f :: "nat ⇒ rat"
  assumes i_mem: "i ∈ A"
  assumes cancel: "L^2 = f i^2"
  assumes eq:
    "L^2 + (∑j∈A - {i}. f j^2) = f i^2 + RHS"
  shows "(∑j∈A - {i}. f j^2) = RHS"
  using eq cancel
  by simp

lemma eliminate_last_square_from_interval:
  fixes f :: "nat ⇒ rat"
  assumes cancel: "L^2 = f n^2"
  assumes eq:
    "L^2 + (∑j∈{0..<n}. f j^2) = f n^2 + RHS"
  shows "(∑j∈{0..<n}. f j^2) = RHS"
  using eq cancel
  by simp

lemma brc_final_rat_from_reduced_identity:
  fixes Lv y0 yv :: rat
  assumes red:
    "Lv^2 = of_nat Λ * y0^2 + of_nat (𝗄 - Λ) * yv^2"
  assumes nz:
    "Lv ≠ 0 ∨ y0 ≠ 0 ∨ yv ≠ 0"
  shows
    "∃q0 q1 q2 :: rat.
       (q0 ≠ 0 ∨ q1 ≠ 0 ∨ q2 ≠ 0) ∧
       q0^2 = of_nat (𝗄 - Λ) * q1^2 + of_nat Λ * q2^2"
proof -
  have eq:
    "Lv^2 = of_nat (𝗄 - Λ) * yv^2 + of_nat Λ * y0^2"
    using red by (simp add: algebra_simps)
  show ?thesis
    using eq nz
    by blast
qed

lemma brc_descent_invariant_from_reduced_identity:
  fixes Lv y0 yv :: rat
  assumes red:
    "Lv^2 = of_nat Λ * y0^2 + of_nat (𝗄 - Λ) * yv^2"
  assumes nz:
    "Lv ≠ 0 ∨ y0 ≠ 0 ∨ yv ≠ 0"
  shows "brc_descent_invariant m"
  unfolding brc_descent_invariant_def
  using brc_final_rat_from_reduced_identity[OF red nz]
  by blast

definition brc_reduced_identity :: "rat ⇒ rat ⇒ rat ⇒ bool" where
  "brc_reduced_identity Lv y0 yv ⟷
     Lv^2 = of_nat Λ * y0^2 + of_nat (𝗄 - Λ) * yv^2"

lemma brc_descent_invariant_from_reduced_identity_def:
  assumes red: "brc_reduced_identity Lv y0 yv"
  assumes nz: "Lv ≠ 0 ∨ y0 ≠ 0 ∨ yv ≠ 0"
  shows "brc_descent_invariant m"
proof -
  have red':
    "Lv^2 = of_nat Λ * y0^2 + of_nat (𝗄 - Λ) * yv^2"
    using red
    unfolding brc_reduced_identity_def
    by simp
  show ?thesis
    using brc_descent_invariant_from_reduced_identity[OF red' nz]
    by simp
qed

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

lemma brc_reduced_identity_conditional:
  fixes a b c d :: nat
  fixes x :: "rat mat"
  assumes v_form: "𝗏 = 4 * w + 1"
  assumes abcd: "𝗄 - Λ = a^2 + b^2 + c^2 + d^2"
  assumes cancel:
    "(∑i∈{0..<𝗏}. (brc_L x i)^2)
     =
     (brc_L x (𝗏 - 1))^2 + y_blocks_sqsum a b c d x w"
  shows
    "brc_reduced_identity (brc_L x (𝗏 - 1)) (brc_y0 x w) (brc_yv x w)"
proof -
  have main:
   "(∑i∈{0..<𝗏}. (brc_L x i)^2)
    =
    of_nat Λ * (brc_y0 x w)^2
    +
    y_blocks_sqsum a b c d x w
    +
    of_nat (𝗄 - Λ) * (brc_yv x w)^2"
    using brc_x_equation_transformed_named[OF v_form abcd, of x] .

  have "(brc_L x (𝗏 - 1))^2 + y_blocks_sqsum a b c d x w
      =
      of_nat Λ * (brc_y0 x w)^2
      +
      y_blocks_sqsum a b c d x w
      +
      of_nat (𝗄 - Λ) * (brc_yv x w)^2"
    using main cancel by simp

  then have "(brc_L x (𝗏 - 1))^2
      =
      of_nat Λ * (brc_y0 x w)^2
      +
      of_nat (𝗄 - Λ) * (brc_yv x w)^2"
    by simp

  then show ?thesis
    unfolding brc_reduced_identity_def
    by simp
qed

lemma brc_v_4w_plus_1_rat_conditional:
  fixes a b c d :: nat
  fixes x :: "rat mat"
  assumes v_form: "𝗏 = 4 * w + 1"
  assumes abcd: "𝗄 - Λ = a^2 + b^2 + c^2 + d^2"
  assumes cancel:
    "(∑i∈{0..<𝗏}. (brc_L x i)^2)
     =
     (brc_L x (𝗏 - 1))^2 + y_blocks_sqsum a b c d x w"
  assumes nz:
    "brc_L x (𝗏 - 1) ≠ 0 ∨ brc_y0 x w ≠ 0 ∨ brc_yv x w ≠ 0"
  shows "brc_descent_invariant w"
proof -
  have red:
    "brc_reduced_identity (brc_L x (𝗏 - 1)) (brc_y0 x w) (brc_yv x w)"
    using brc_reduced_identity_conditional[OF v_form abcd cancel] .
  show ?thesis
    using brc_descent_invariant_from_reduced_identity_def[OF red nz]
    by simp
qed

lemma brc_v_4w_plus_1_rat_conditional_exists_abcd:
  fixes x :: "rat mat"
  assumes v_form: "𝗏 = 4 * w + 1"
  assumes cancel:
    "⋀a b c d.
      𝗄 - Λ = a^2 + b^2 + c^2 + d^2 ⟹
      (∑i∈{0..<𝗏}. (brc_L x i)^2)
       =
      (brc_L x (𝗏 - 1))^2 + y_blocks_sqsum a b c d x w"
  assumes nz:
    "brc_L x (𝗏 - 1) ≠ 0 ∨ brc_y0 x w ≠ 0 ∨ brc_yv x w ≠ 0"
  shows "brc_descent_invariant w"
proof -
  obtain a b c d :: nat where abcd:
    "𝗄 - Λ = a^2 + b^2 + c^2 + d^2"
    using sum_of_four_squares[of "𝗄 - Λ"]
    by blast

  have cancel':
    "(∑i∈{0..<𝗏}. (brc_L x i)^2)
     =
     (brc_L x (𝗏 - 1))^2 + y_blocks_sqsum a b c d x w"
    using cancel[OF abcd] .

  show ?thesis
    using brc_v_4w_plus_1_rat_conditional[OF v_form abcd cancel' nz] .
qed

definition brc_cancel_condition ::
  "nat ⇒ nat ⇒ nat ⇒ nat ⇒ rat mat ⇒ nat ⇒ bool" where
  "brc_cancel_condition a b c d x w ⟷
     (∑i∈{0..<𝗏}. (brc_L x i)^2)
     =
     (brc_L x (𝗏 - 1))^2 + y_blocks_sqsum a b c d x w"

lemma brc_v_4w_plus_1_rat_from_cancel_condition:
  fixes a b c d :: nat
  fixes x :: "rat mat"
  assumes v_form: "𝗏 = 4 * w + 1"
  assumes abcd: "𝗄 - Λ = a^2 + b^2 + c^2 + d^2"
  assumes cancel: "brc_cancel_condition a b c d x w"
  assumes nz:
    "brc_L x (𝗏 - 1) ≠ 0 ∨ brc_y0 x w ≠ 0 ∨ brc_yv x w ≠ 0"
  shows "brc_descent_invariant w"
proof -
  have cancel':
    "(∑i∈{0..<𝗏}. (brc_L x i)^2)
     =
     (brc_L x (𝗏 - 1))^2 + y_blocks_sqsum a b c d x w"
    using cancel
    unfolding brc_cancel_condition_def
    by simp

  show ?thesis
    using brc_v_4w_plus_1_rat_conditional[OF v_form abcd cancel' nz] .
qed

theorem brc_v_4w_plus_1_rat_conditional_final:
  assumes v_form: "𝗏 = 4 * w + 1"
  assumes exists_cancel:
    "∃a b c d x.
       𝗄 - Λ = a^2 + b^2 + c^2 + d^2 ∧
       brc_cancel_condition a b c d x w ∧
       (brc_L x (𝗏 - 1) ≠ 0 ∨ brc_y0 x w ≠ 0 ∨ brc_yv x w ≠ 0)"
  shows "brc_descent_invariant w"
proof -
  obtain a b c d x where abcd:
    "𝗄 - Λ = a^2 + b^2 + c^2 + d^2"
    and cancel:
    "brc_cancel_condition a b c d x w"
    and nz:
    "brc_L x (𝗏 - 1) ≠ 0 ∨ brc_y0 x w ≠ 0 ∨ brc_yv x w ≠ 0"
    using exists_cancel by blast

  show ?thesis
    using brc_v_4w_plus_1_rat_from_cancel_condition[OF v_form abcd cancel nz] .
qed

lemma brc_cancel_condition_from_indexed_cancel:
  fixes a b c d :: nat
  fixes x :: "rat mat"
  assumes v_form: "𝗏 = 4 * w + 1"
  assumes cancel_sum:
    "(∑i∈{0..<4*w}. (brc_L x i)^2)
     =
     y_blocks_sqsum a b c d x w"
  shows "brc_cancel_condition a b c d x w"
proof -
  have v_suc: "𝗏 = Suc (4*w)"
    using v_form by simp

  have split:
    "(∑i∈{0..<𝗏}. (brc_L x i)^2)
     =
     (∑i∈{0..<4*w}. (brc_L x i)^2)
     + (brc_L x (4*w))^2"
    using v_suc
    by (simp add: sum.atLeast0_lessThan_Suc)

  have last: "𝗏 - 1 = 4*w"
    using v_form by simp

  show ?thesis
    unfolding brc_cancel_condition_def
    using split cancel_sum last
    by (simp add: algebra_simps)
qed

theorem brc_v_4w_plus_1_rat_from_indexed_cancel:
  assumes v_form: "𝗏 = 4 * w + 1"
  assumes exists_indexed_cancel:
    "∃a b c d x.
       𝗄 - Λ = a^2 + b^2 + c^2 + d^2 ∧
       (∑i∈{0..<4*w}. (brc_L x i)^2)
        =
       y_blocks_sqsum a b c d x w ∧
       (brc_L x (𝗏 - 1) ≠ 0 ∨ brc_y0 x w ≠ 0 ∨ brc_yv x w ≠ 0)"
  shows "brc_descent_invariant w"
proof -
  obtain a b c d x where abcd:
    "𝗄 - Λ = a^2 + b^2 + c^2 + d^2"
    and cancel_sum:
    "(∑i∈{0..<4*w}. (brc_L x i)^2)
      =
     y_blocks_sqsum a b c d x w"
    and nz:
    "brc_L x (𝗏 - 1) ≠ 0 ∨ brc_y0 x w ≠ 0 ∨ brc_yv x w ≠ 0"
    using exists_indexed_cancel by blast

  have cancel_cond:
    "brc_cancel_condition a b c d x w"
    using brc_cancel_condition_from_indexed_cancel[
      OF v_form cancel_sum] .

  show ?thesis
    using brc_v_4w_plus_1_rat_from_cancel_condition[
      OF v_form abcd cancel_cond nz] .
qed

lemma linear_square_can_be_matched:
  fixes e rest :: rat
  shows "∃y :: rat. (e * y + rest)^2 = y^2"
  using choose_y_square_cancel[of e rest]
  by blast

lemma eliminate_one_linear_variable:
  fixes e rest :: rat
  shows "∃y :: rat. (e * y + rest)^2 = y^2"
proof -
  obtain y :: rat where "(e * y + rest)^2 = y^2"
    using choose_y_square_cancel[of e rest] by blast
  then show ?thesis
    by blast
qed

lemma eliminate_list_linear_variables:
  fixes e rest :: "nat ⇒ rat"
  shows "∃y :: nat ⇒ rat.
    ∀i < n. (e i * y i + rest i)^2 = (y i)^2"
proof -
  have "∀i<n. ∃yi :: rat. (e i * yi + rest i)^2 = yi^2"
    using choose_y_square_cancel by blast
  then obtain y where "∀i<n. (e i * y i + rest i)^2 = y i^2"
    by metis
  then show ?thesis
    by blast
qed

lemma eliminate_list_linear_variables_sum:
  fixes e rest :: "nat ⇒ rat"
  shows "∃y :: nat ⇒ rat.
    (∑i∈{0..<n}. (e i * y i + rest i)^2)
    =
    (∑i∈{0..<n}. (y i)^2)"
proof -
  obtain y :: "nat ⇒ rat" where h:
    "∀i < n. (e i * y i + rest i)^2 = (y i)^2"
    using eliminate_list_linear_variables[where n=n and e=e and rest=rest]
    by blast

  have "(∑i∈{0..<n}. (e i * y i + rest i)^2)
      =
        (∑i∈{0..<n}. (y i)^2)"
    using h by simp

  then show ?thesis
    by blast
qed

definition brc_elimination_witness ::
  "nat ⇒ nat ⇒ nat ⇒ nat ⇒ rat mat ⇒ nat ⇒ bool" where
  "brc_elimination_witness a b c d x w ⟷
     (∑i∈{0..<4*w}. (brc_L x i)^2)
      =
     y_blocks_sqsum a b c d x w"

lemma brc_exists_indexed_cancel_from_elimination_witness:
  assumes v_form: "𝗏 = 4 * w + 1"
  assumes witness:
    "∃a b c d x.
       𝗄 - Λ = a^2 + b^2 + c^2 + d^2 ∧
       brc_elimination_witness a b c d x w"
  shows "∃a b c d x.
       𝗄 - Λ = a^2 + b^2 + c^2 + d^2 ∧
       (∑i∈{0..<4*w}. (brc_L x i)^2)
        =
       y_blocks_sqsum a b c d x w"
  using witness
  unfolding brc_elimination_witness_def
  by blast

lemma brc_elimination_witness_exists_from_nonzero:
  assumes v_form: "𝗏 = 4 * w + 1"
  assumes witness:
    "∃a b c d x.
       𝗄 - Λ = a^2 + b^2 + c^2 + d^2 ∧
       brc_elimination_witness a b c d x w ∧
       (brc_L x (𝗏 - 1) ≠ 0 ∨
        brc_y0 x w ≠ 0 ∨
        brc_yv x w ≠ 0)"
  shows "∃a b c d x.
       𝗄 - Λ = a^2 + b^2 + c^2 + d^2 ∧
       brc_elimination_witness a b c d x w ∧
       (brc_L x (𝗏 - 1) ≠ 0 ∨
        brc_y0 x w ≠ 0 ∨
        brc_yv x w ≠ 0)"
  using witness .


lemma brc_exists_indexed_cancel:
  assumes v_form: "𝗏 = 4 * w + 1"
  assumes witness:
    "∃a b c d x.
       𝗄 - Λ = a^2 + b^2 + c^2 + d^2 ∧
       brc_elimination_witness a b c d x w ∧
       (brc_L x (𝗏 - 1) ≠ 0 ∨
        brc_y0 x w ≠ 0 ∨
        brc_yv x w ≠ 0)"
  shows "∃a b c d x.
       𝗄 - Λ = a^2 + b^2 + c^2 + d^2 ∧
       (∑i∈{0..<4*w}. (brc_L x i)^2)
        =
       y_blocks_sqsum a b c d x w ∧
       (brc_L x (𝗏 - 1) ≠ 0 ∨
        brc_y0 x w ≠ 0 ∨
        brc_yv x w ≠ 0)"
proof -
  obtain a b c d x where abcd:
    "𝗄 - Λ = a^2 + b^2 + c^2 + d^2"
    and elim:
    "brc_elimination_witness a b c d x w"
    and nz:
    "brc_L x (𝗏 - 1) ≠ 0 ∨ brc_y0 x w ≠ 0 ∨ brc_yv x w ≠ 0"
    using witness by blast

  have cancel:
    "(∑i∈{0..<4*w}. (brc_L x i)^2)
      =
     y_blocks_sqsum a b c d x w"
    using elim
    unfolding brc_elimination_witness_def
    by simp

  show ?thesis
    using abcd cancel nz
    by blast
qed

theorem brc_v_4w_plus_1_rat_from_nonzero_elimination_witness:
  assumes v_form: "𝗏 = 4 * w + 1"
  assumes witness:
    "∃a b c d x.
       𝗄 - Λ = a^2 + b^2 + c^2 + d^2 ∧
       brc_elimination_witness a b c d x w ∧
       (brc_L x (𝗏 - 1) ≠ 0 ∨
        brc_y0 x w ≠ 0 ∨
        brc_yv x w ≠ 0)"
  shows "brc_descent_invariant w"
proof -
  have indexed:
    "∃a b c d x.
       𝗄 - Λ = a^2 + b^2 + c^2 + d^2 ∧
       (∑i∈{0..<4*w}. (brc_L x i)^2)
        =
       y_blocks_sqsum a b c d x w ∧
       (brc_L x (𝗏 - 1) ≠ 0 ∨
        brc_y0 x w ≠ 0 ∨
        brc_yv x w ≠ 0)"
    using brc_exists_indexed_cancel[OF v_form witness] .

  show ?thesis
    using brc_v_4w_plus_1_rat_from_indexed_cancel[OF v_form indexed] .
qed

definition brc_nonzero_elimination_witness ::
  "nat ⇒ nat ⇒ nat ⇒ nat ⇒ rat mat ⇒ nat ⇒ bool" where
  "brc_nonzero_elimination_witness a b c d x w ⟷
     brc_elimination_witness a b c d x w ∧
     (brc_L x (𝗏 - 1) ≠ 0 ∨
      brc_y0 x w ≠ 0 ∨
      brc_yv x w ≠ 0)"

theorem brc_v_4w_plus_1_rat_from_nonzero_witness:
  assumes v_form: "𝗏 = 4 * w + 1"
  assumes witness:
    "∃a b c d x.
       𝗄 - Λ = a^2 + b^2 + c^2 + d^2 ∧
       brc_nonzero_elimination_witness a b c d x w"
  shows "brc_descent_invariant w"
proof -
  obtain a b c d x where abcd:
    "𝗄 - Λ = a^2 + b^2 + c^2 + d^2"
    and wit:
    "brc_nonzero_elimination_witness a b c d x w"
    using witness by blast

  have elim:
    "brc_elimination_witness a b c d x w"
    using wit
    unfolding brc_nonzero_elimination_witness_def
    by simp

  have nz:
    "brc_L x (𝗏 - 1) ≠ 0 ∨
     brc_y0 x w ≠ 0 ∨
     brc_yv x w ≠ 0"
    using wit
    unfolding brc_nonzero_elimination_witness_def
    by simp

  have witness':
    "∃a b c d x.
       𝗄 - Λ = a^2 + b^2 + c^2 + d^2 ∧
       brc_elimination_witness a b c d x w ∧
       (brc_L x (𝗏 - 1) ≠ 0 ∨
        brc_y0 x w ≠ 0 ∨
        brc_yv x w ≠ 0)"
    using abcd elim nz
    by blast

  show ?thesis
    using brc_v_4w_plus_1_rat_from_nonzero_elimination_witness[
      OF v_form witness']
    .
qed

lemma four_sq_nat_coeff_nonzero_rat:
  fixes n :: nat
  assumes "n ≠ 0"
  shows "of_nat n ≠ (0 :: rat)"
  using assms by simp

lemma y_reversible_zero_imp_zero:
  fixes a b c d :: nat
  fixes x0 x1 x2 x3 :: rat
  assumes nzsum: "a^2 + b^2 + c^2 + d^2 ≠ 0"
  assumes yz: "y_of ((a,b,c,d),(x0,x1,x2,x3)) = (0,0,0,0)"
  shows "x0 = 0 ∧ x1 = 0 ∧ x2 = 0 ∧ x3 = 0"
proof -
  let ?n = "a^2 + b^2 + c^2 + d^2"

  have norm:
    "(one_of (y_of ((a,b,c,d),(x0,x1,x2,x3))))^2 +
     (two_of (y_of ((a,b,c,d),(x0,x1,x2,x3))))^2 +
     (three_of (y_of ((a,b,c,d),(x0,x1,x2,x3))))^2 +
     (four_of (y_of ((a,b,c,d),(x0,x1,x2,x3))))^2
     =
     of_nat ?n * (x0^2 + x1^2 + x2^2 + x3^2)"
    using y_norm_identity[of ?n a b c d x0 x1 x2 x3]
    by simp

  have left0:
    "(one_of (y_of ((a,b,c,d),(x0,x1,x2,x3))))^2 +
     (two_of (y_of ((a,b,c,d),(x0,x1,x2,x3))))^2 +
     (three_of (y_of ((a,b,c,d),(x0,x1,x2,x3))))^2 +
     (four_of (y_of ((a,b,c,d),(x0,x1,x2,x3))))^2 = 0"
    using yz by simp

  have sqsum0:
    "x0^2 + x1^2 + x2^2 + x3^2 = 0"
  proof -
    have "of_nat ?n * (x0^2 + x1^2 + x2^2 + x3^2) = 0"
      using norm left0 by simp
    moreover have "of_nat ?n ≠ (0::rat)"
      using four_sq_nat_coeff_nonzero_rat[of ?n] nzsum
      by blast
    ultimately show ?thesis
      by simp
  qed

  have sqsum_nonneg:
    "0 ≤ x0^2 ∧ 0 ≤ x1^2 ∧ 0 ≤ x2^2 ∧ 0 ≤ x3^2"
    by simp

  have x0sq: "x0^2 = 0"
    using sqsum0 sqsum_nonneg by linarith
  have x1sq: "x1^2 = 0"
    using sqsum0 sqsum_nonneg by linarith
  have x2sq: "x2^2 = 0"
    using sqsum0 sqsum_nonneg by linarith
  have x3sq: "x3^2 = 0"
    using sqsum0 sqsum_nonneg by linarith

  have x0z: "x0 = 0" using x0sq by simp
  have x1z: "x1 = 0" using x1sq by simp
  have x2z: "x2 = 0" using x2sq by simp
  have x3z: "x3 = 0" using x3sq by simp

  show ?thesis
    using x0z x1z x2z x3z by simp
qed

lemma y_reversible_nonzero:
  fixes a b c d :: nat
  fixes x0 x1 x2 x3 :: rat
  assumes nzsum: "a^2 + b^2 + c^2 + d^2 ≠ 0"
  assumes nz: "x0 ≠ 0 ∨ x1 ≠ 0 ∨ x2 ≠ 0 ∨ x3 ≠ 0"
  shows "y_of ((a,b,c,d),(x0,x1,x2,x3)) ≠ (0,0,0,0)"
proof
  assume yz: "y_of ((a,b,c,d),(x0,x1,x2,x3)) = (0,0,0,0)"
  have "x0 = 0 ∧ x1 = 0 ∧ x2 = 0 ∧ x3 = 0"
    using y_reversible_zero_imp_zero[OF nzsum yz] .
  thus False
    using nz by simp
qed

lemma y_block_sqsum_zero_imp_x_block_zero:
  fixes a b c d :: nat
  fixes x :: "rat mat"
  assumes nzsum: "a^2 + b^2 + c^2 + d^2 ≠ 0"
  assumes z: "y_block_sqsum a b c d x h = 0"
  shows
    "x $$ (4*h,0) = 0 ∧
     x $$ (4*h+1,0) = 0 ∧
     x $$ (4*h+2,0) = 0 ∧
     x $$ (4*h+3,0) = 0"
proof -
  let ?Y =
    "y_of ((a,b,c,d),
      (x $$ (4*h,0),
       x $$ (4*h+1,0),
       x $$ (4*h+2,0),
       x $$ (4*h+3,0)))"

  have sum0:
    "(one_of ?Y)^2 + (two_of ?Y)^2 + (three_of ?Y)^2 + (four_of ?Y)^2 = 0"
    using z
    unfolding y_block_sqsum_def
    by simp

  have nonneg:
    "0 ≤ (one_of ?Y)^2 ∧
     0 ≤ (two_of ?Y)^2 ∧
     0 ≤ (three_of ?Y)^2 ∧
     0 ≤ (four_of ?Y)^2"
    by simp

  have y0sq: "(one_of ?Y)^2 = 0"
    using sum0 nonneg by linarith
  have y1sq: "(two_of ?Y)^2 = 0"
    using sum0 nonneg by linarith
  have y2sq: "(three_of ?Y)^2 = 0"
    using sum0 nonneg by linarith
  have y3sq: "(four_of ?Y)^2 = 0"
    using sum0 nonneg by linarith

  have yzero: "?Y = (0,0,0,0)"
    using y0sq y1sq y2sq y3sq
    by (cases ?Y) simp

  show ?thesis
    using y_reversible_zero_imp_zero[OF nzsum yzero]
    by simp
qed

lemma y_block_nonzero:
  fixes a b c d :: nat
  fixes x :: "rat mat"
  assumes nzsum: "a^2 + b^2 + c^2 + d^2 ≠ 0"
  assumes nz:
    "x $$ (4*h,0) ≠ 0 ∨
     x $$ (4*h+1,0) ≠ 0 ∨
     x $$ (4*h+2,0) ≠ 0 ∨
     x $$ (4*h+3,0) ≠ 0"
  shows "y_block_sqsum a b c d x h ≠ 0"
proof
  assume z: "y_block_sqsum a b c d x h = 0"
  have
    "x $$ (4*h,0) = 0 ∧
     x $$ (4*h+1,0) = 0 ∧
     x $$ (4*h+2,0) = 0 ∧
     x $$ (4*h+3,0) = 0"
    using y_block_sqsum_zero_imp_x_block_zero[OF nzsum z] .
  then show False
    using nz by simp
qed

lemma y_blocks_sqsum_zero_imp_x_blocks_zero:
  fixes a b c d :: nat
  fixes x :: "rat mat"
  assumes nzsum: "a^2 + b^2 + c^2 + d^2 ≠ 0"
  assumes z: "y_blocks_sqsum a b c d x w = 0"
  assumes hw: "h < w"
  shows
    "x $$ (4*h,0) = 0 ∧
     x $$ (4*h+1,0) = 0 ∧
     x $$ (4*h+2,0) = 0 ∧
     x $$ (4*h+3,0) = 0"
proof -
  have block0: "y_block_sqsum a b c d x h = 0"
  proof -
    have nonneg: "⋀r. r ∈ {0..<w} ⟹ 0 ≤ y_block_sqsum a b c d x r"
      unfolding y_block_sqsum_def
      by simp
    have "y_blocks_sqsum a b c d x w =
          (∑r∈{0..<w}. y_block_sqsum a b c d x r)"
      unfolding y_blocks_sqsum_def by simp
    then have sum0:
      "(∑r∈{0..<w}. y_block_sqsum a b c d x r) = 0"
      using z by simp
    have "0 ≤ y_block_sqsum a b c d x h"
      using nonneg hw by simp
    moreover have "y_block_sqsum a b c d x h ≤
          (∑r∈{0..<w}. y_block_sqsum a b c d x r)"
    proof -
      have hmem: "h ∈ {0..<w}"
        using hw by simp
      have fin: "finite {0..<w}"
        by simp
      have
        "(∑r∈{0..<w}. y_block_sqsum a b c d x r)
         =
         y_block_sqsum a b c d x h
         +
         (∑r∈{0..<w} - {h}. y_block_sqsum a b c d x r)"
        using sum.remove[OF fin hmem, of "y_block_sqsum a b c d x"]
        by (simp add: algebra_simps)
      moreover have "0 ≤ (∑r∈{0..<w} - {h}. y_block_sqsum a b c d x r)"
      proof (rule sum_nonneg)
        fix r
        assume rmem: "r ∈ {0..<w} - {h}"
        then have "r < w"
          by simp
        then show "0 ≤ y_block_sqsum a b c d x r"
          using nonneg by simp
      qed
      ultimately show ?thesis
        by simp
    qed
    ultimately show ?thesis
      using sum0 by simp
  qed

  show ?thesis
    using y_block_sqsum_zero_imp_x_block_zero[OF nzsum block0] .
qed

lemma x_head_block_nonzero_imp_y_blocks_sqsum_nonzero:
  fixes a b c d :: nat
  fixes x :: "rat mat"
  assumes nzsum: "a^2 + b^2 + c^2 + d^2 ≠ 0"
  assumes hw: "h < w"
  assumes nz:
    "x $$ (4*h,0) ≠ 0 ∨
     x $$ (4*h+1,0) ≠ 0 ∨
     x $$ (4*h+2,0) ≠ 0 ∨
     x $$ (4*h+3,0) ≠ 0"
  shows "y_blocks_sqsum a b c d x w ≠ 0"
proof
  assume z: "y_blocks_sqsum a b c d x w = 0"
  have
    "x $$ (4*h,0) = 0 ∧
     x $$ (4*h+1,0) = 0 ∧
     x $$ (4*h+2,0) = 0 ∧
     x $$ (4*h+3,0) = 0"
    using y_blocks_sqsum_zero_imp_x_blocks_zero[OF nzsum z hw] .
  then show False
    using nz by simp
qed

lemma brc_reduced_identity_zero_triple:
  assumes red:
    "brc_reduced_identity Lv y0 yv"
  assumes z:
    "Lv = 0" "y0 = 0" "yv = 0"
  shows True
  using red z
  by simp

lemma brc_nonzero_witnessI:
  fixes a b c d :: nat
  fixes x :: "rat mat"
  assumes elim: "brc_elimination_witness a b c d x w"
  assumes nz:
    "brc_L x (𝗏 - 1) ≠ 0 ∨
     brc_y0 x w ≠ 0 ∨
     brc_yv x w ≠ 0"
  shows "brc_nonzero_elimination_witness a b c d x w"
  using elim nz
  unfolding brc_nonzero_elimination_witness_def
  by simp

lemma brc_nonzero_elimination_witness_exists_from_x:
  assumes v_form: "𝗏 = 4 * w + 1"
  assumes abcd: "𝗄 - Λ = a^2 + b^2 + c^2 + d^2"
  assumes elim: "brc_elimination_witness a b c d x w"
  assumes nz:
    "brc_L x (𝗏 - 1) ≠ 0 ∨
     brc_y0 x w ≠ 0 ∨
     brc_yv x w ≠ 0"
  shows "∃a b c d x.
       𝗄 - Λ = a^2 + b^2 + c^2 + d^2 ∧
       brc_nonzero_elimination_witness a b c d x w"
proof -
  have "brc_nonzero_elimination_witness a b c d x w"
    using brc_nonzero_witnessI[OF elim nz] .
  then show ?thesis
    using abcd by blast
qed

lemma brc_v_4w_plus_1_rat_from_constructed_x:
  fixes a b c d :: nat
  fixes x :: "rat mat"
  assumes v_form: "𝗏 = 4 * w + 1"
  assumes abcd: "𝗄 - Λ = a^2 + b^2 + c^2 + d^2"
  assumes elim: "brc_elimination_witness a b c d x w"
  assumes nz:
    "brc_L x (𝗏 - 1) ≠ 0 ∨
     brc_y0 x w ≠ 0 ∨
     brc_yv x w ≠ 0"
  shows "brc_descent_invariant w"
proof -
  have witness:
    "∃a b c d x.
       𝗄 - Λ = a^2 + b^2 + c^2 + d^2 ∧
       brc_nonzero_elimination_witness a b c d x w"
    using brc_nonzero_elimination_witness_exists_from_x[
      OF v_form abcd elim nz]
    .

  show ?thesis
    using brc_v_4w_plus_1_rat_from_nonzero_witness[OF v_form witness] .
qed

lemma brc_nz_from_x_last_one:
  assumes last_one: "x_last x w = 1"
  shows "brc_L x (𝗏 - 1) ≠ 0 ∨ brc_y0 x w ≠ 0 ∨ brc_yv x w ≠ 0"
  unfolding brc_yv_def
  using last_one
  by simp

lemma brc_v_4w_plus_1_rat_from_constructed_x_last_one:
  fixes a b c d :: nat
  fixes x :: "rat mat"
  assumes v_form: "𝗏 = 4 * w + 1"
  assumes abcd: "𝗄 - Λ = a^2 + b^2 + c^2 + d^2"
  assumes elim: "brc_elimination_witness a b c d x w"
  assumes last_one: "x_last x w = 1"
  shows "brc_descent_invariant w"
proof -
  have nz:
    "brc_L x (𝗏 - 1) ≠ 0 ∨ brc_y0 x w ≠ 0 ∨ brc_yv x w ≠ 0"
    using brc_nz_from_x_last_one[OF last_one] .

  show ?thesis
    using brc_v_4w_plus_1_rat_from_constructed_x[
      OF v_form abcd elim nz]
    .
qed

definition brc_last_one_elimination_witness ::
  "nat ⇒ nat ⇒ nat ⇒ nat ⇒ rat mat ⇒ nat ⇒ bool" where
  "brc_last_one_elimination_witness a b c d x w ⟷
     brc_elimination_witness a b c d x w ∧
     x_last x w = 1"

lemma brc_v_4w_plus_1_rat_from_last_one_elimination_witness:
  assumes v_form: "𝗏 = 4 * w + 1"
  assumes witness:
    "∃a b c d x.
       𝗄 - Λ = a^2 + b^2 + c^2 + d^2 ∧
       brc_last_one_elimination_witness a b c d x w"
  shows "brc_descent_invariant w"
proof -
  obtain a b c d x where abcd:
    "𝗄 - Λ = a^2 + b^2 + c^2 + d^2"
    and wit:
    "brc_last_one_elimination_witness a b c d x w"
    using witness by blast

  have elim:
    "brc_elimination_witness a b c d x w"
    using wit
    unfolding brc_last_one_elimination_witness_def
    by simp

  have last_one:
    "x_last x w = 1"
    using wit
    unfolding brc_last_one_elimination_witness_def
    by simp

  show ?thesis
    using brc_v_4w_plus_1_rat_from_constructed_x_last_one[
      OF v_form abcd elim last_one]
    .
qed

definition brc_blockwise_elimination_witness ::
  "nat ⇒ nat ⇒ nat ⇒ nat ⇒ rat mat ⇒ nat ⇒ bool" where
  "brc_blockwise_elimination_witness a b c d x w ⟷
     x_last x w = 1 ∧
     (∀h < w.
        (brc_L x (4*h))^2 +
        (brc_L x (4*h + 1))^2 +
        (brc_L x (4*h + 2))^2 +
        (brc_L x (4*h + 3))^2
        =
        y_block_sqsum a b c d x h)"

lemma eliminate_four_linear_variables:
  fixes e0 e1 e2 e3 r0 r1 r2 r3 :: rat
  shows "∃y0 y1 y2 y3 :: rat.
    (e0*y0 + r0)^2 +
    (e1*y1 + r1)^2 +
    (e2*y2 + r2)^2 +
    (e3*y3 + r3)^2
    =
    y0^2 + y1^2 + y2^2 + y3^2"
proof -
  obtain y0 where y0: "(e0*y0 + r0)^2 = y0^2"
    using choose_y_square_cancel[of e0 r0] by blast
  obtain y1 where y1: "(e1*y1 + r1)^2 = y1^2"
    using choose_y_square_cancel[of e1 r1] by blast
  obtain y2 where y2: "(e2*y2 + r2)^2 = y2^2"
    using choose_y_square_cancel[of e2 r2] by blast
  obtain y3 where y3: "(e3*y3 + r3)^2 = y3^2"
    using choose_y_square_cancel[of e3 r3] by blast
  show ?thesis
  proof
    show "∃y1 y2 y3.
      (e0 * y0 + r0)^2 + (e1 * y1 + r1)^2 +
      (e2 * y2 + r2)^2 + (e3 * y3 + r3)^2 =
      y0^2 + y1^2 + y2^2 + y3^2"
    proof
      show "∃y2 y3.
        (e0 * y0 + r0)^2 + (e1 * y1 + r1)^2 +
        (e2 * y2 + r2)^2 + (e3 * y3 + r3)^2 =
        y0^2 + y1^2 + y2^2 + y3^2"
      proof
        show "∃y3.
          (e0 * y0 + r0)^2 + (e1 * y1 + r1)^2 +
          (e2 * y2 + r2)^2 + (e3 * y3 + r3)^2 =
          y0^2 + y1^2 + y2^2 + y3^2"
        proof
          show "(e0 * y0 + r0)^2 + (e1 * y1 + r1)^2 +
                (e2 * y2 + r2)^2 + (e3 * y3 + r3)^2 =
                y0^2 + y1^2 + y2^2 + y3^2"
            using y0 y1 y2 y3
            by simp
        qed
      qed
    qed
  qed
qed

definition scale_x :: "rat ⇒ rat mat ⇒ rat mat" where
  "scale_x c x = mat 𝗏 1 (λ(i,j). c * x $$ (i,j))"

lemma scale_x_entry:
  assumes i_lt: "i < 𝗏"
  shows "scale_x c x $$ (i,0) = c * x $$ (i,0)"
  unfolding scale_x_def
  using i_lt
  by simp

lemma brc_L_scale:
  assumes i_lt: "i < 𝗏"
  shows "brc_L (scale_x c x) i = c * brc_L x i"
proof -
  have "brc_L (scale_x c x) i =
        (∑h∈{0..<𝗏}. of_int (N $$ (h,i)) * (c * x $$ (h,0)))"
    unfolding brc_L_def
    by (simp add: scale_x_entry)
  also have "... =
        c * (∑h∈{0..<𝗏}. of_int (N $$ (h,i)) * x $$ (h,0))"
    by (simp add: sum_distrib_left algebra_simps)
  finally show ?thesis
    unfolding brc_L_def
    by simp
qed

lemma x_last_scale:
  assumes v_form: "𝗏 = 4 * w + 1"
  shows "x_last (scale_x c x) w = c * x_last x w"
proof -
  have "4*w < 𝗏"
    using v_form by simp
  then show ?thesis
    unfolding x_last_def
    by (simp add: scale_x_entry)
qed

lemma y_block_sqsum_scale:
  assumes h_lt: "h < w"
  assumes v_form: "𝗏 = 4 * w + 1"
  shows "y_block_sqsum a b c d (scale_x r x) h =
         r^2 * y_block_sqsum a b c d x h"
proof -
  have b0: "4*h < 𝗏"
    using h_lt v_form by simp
  have b1: "4*h + 1 < 𝗏"
    using h_lt v_form by simp
  have b2: "4*h + 2 < 𝗏"
    using h_lt v_form by simp
  have b3: "4*h + 3 < 𝗏"
    using h_lt v_form by simp

  show ?thesis
    unfolding y_block_sqsum_def
    using b0 b1 b2 b3
    by (simp add: scale_x_entry power2_eq_square algebra_simps)
qed

lemma y_blocks_sqsum_scale:
  assumes v_form: "𝗏 = 4 * w + 1"
  shows "y_blocks_sqsum a b c d (scale_x r x) w =
         r^2 * y_blocks_sqsum a b c d x w"
proof -
  have "⋀h. h ∈ {0..<w} ⟹
        y_block_sqsum a b c d (scale_x r x) h =
        r^2 * y_block_sqsum a b c d x h"
    using y_block_sqsum_scale[OF _ v_form, of _ a b c d r x]
    by simp
  then show ?thesis
    unfolding y_blocks_sqsum_def
    by (simp add: sum_distrib_left)
qed

lemma brc_elimination_witness_scale:
  assumes v_form: "𝗏 = 4 * w + 1"
  assumes elim: "brc_elimination_witness a b c d x w"
  shows "brc_elimination_witness a b c d (scale_x r x) w"
proof -
  have left:
    "(∑i∈{0..<4*w}. (brc_L (scale_x r x) i)^2)
     =
     r^2 * (∑i∈{0..<4*w}. (brc_L x i)^2)"
  proof -
    have "⋀i. i ∈ {0..<4*w} ⟹ brc_L (scale_x r x) i = r * brc_L x i"
    proof -
      fix i
      assume i_mem: "i ∈ {0..<4*w}"
      have i_lt_v: "i < 𝗏"
        using i_mem v_form by simp
      show "brc_L (scale_x r x) i = r * brc_L x i"
        using brc_L_scale[OF i_lt_v, of r x] .
    qed
    then show ?thesis
      by (simp add: power2_eq_square sum_distrib_left algebra_simps)
  qed

  have right:
    "y_blocks_sqsum a b c d (scale_x r x) w =
     r^2 * y_blocks_sqsum a b c d x w"
    using y_blocks_sqsum_scale[OF v_form, of a b c d r x] .

  show ?thesis
    using elim left right
    unfolding brc_elimination_witness_def
    by simp
qed

lemma brc_yv_scale:
  assumes v_form: "𝗏 = 4 * w + 1"
  shows "brc_yv (scale_x r x) w = r * brc_yv x w"
  unfolding brc_yv_def
  using x_last_scale[OF v_form, of r x]
  by simp

lemma brc_last_one_witness_from_nonzero_yv:
  assumes v_form: "𝗏 = 4 * w + 1"
  assumes elim: "brc_elimination_witness a b c d x w"
  assumes nz: "brc_yv x w ≠ 0"
  shows "brc_last_one_elimination_witness a b c d
           (scale_x (1 / brc_yv x w) x) w"
proof -
  have elim_scaled:
    "brc_elimination_witness a b c d
       (scale_x (1 / brc_yv x w) x) w"
    using brc_elimination_witness_scale[OF v_form elim] .

  have last_one:
    "x_last (scale_x (1 / brc_yv x w) x) w = 1"
    using x_last_scale[OF v_form, of "1 / brc_yv x w" x] nz
    unfolding brc_yv_def
    by simp

  show ?thesis
    unfolding brc_last_one_elimination_witness_def
    using elim_scaled last_one
    by simp
qed

lemma brc_last_one_elimination_witness_exists_from_yv_nonzero:
  assumes v_form: "𝗏 = 4 * w + 1"
  assumes witness:
    "∃a b c d x.
       𝗄 - Λ = a^2 + b^2 + c^2 + d^2 ∧
       brc_elimination_witness a b c d x w ∧
       brc_yv x w ≠ 0"
  shows "∃a b c d x.
       𝗄 - Λ = a^2 + b^2 + c^2 + d^2 ∧
       brc_last_one_elimination_witness a b c d x w"
proof -
  obtain a b c d x where abcd:
    "𝗄 - Λ = a^2 + b^2 + c^2 + d^2"
    and elim:
    "brc_elimination_witness a b c d x w"
    and nz:
    "brc_yv x w ≠ 0"
    using witness by blast

  have last_one:
    "brc_last_one_elimination_witness a b c d
       (scale_x (1 / brc_yv x w) x) w"
    using brc_last_one_witness_from_nonzero_yv[OF v_form elim nz] .

  show ?thesis
    using abcd last_one by blast
qed

lemma brc_v_4w_plus_1_rat_from_yv_nonzero_witness:
  assumes v_form: "𝗏 = 4 * w + 1"
  assumes witness:
    "∃a b c d x.
       𝗄 - Λ = a^2 + b^2 + c^2 + d^2 ∧
       brc_elimination_witness a b c d x w ∧
       brc_yv x w ≠ 0"
  shows "brc_descent_invariant w"
proof -
  have last_one_witness:
    "∃a b c d x.
       𝗄 - Λ = a^2 + b^2 + c^2 + d^2 ∧
       brc_last_one_elimination_witness a b c d x w"
    using brc_last_one_elimination_witness_exists_from_yv_nonzero[
      OF v_form witness] .

  show ?thesis
    using brc_v_4w_plus_1_rat_from_last_one_elimination_witness[
      OF v_form last_one_witness]
    .
qed

definition last_unit_x :: "nat ⇒ rat mat" where
  "last_unit_x w =
     mat 𝗏 1 (λ(i,j). if j = 0 ∧ i = 4*w then 1 else 0)"

lemma last_unit_x_last:
  assumes v_form: "𝗏 = 4 * w + 1"
  shows "brc_yv (last_unit_x w) w = 1"
proof -
  have "4*w < 𝗏"
    using v_form by simp
  then show ?thesis
    unfolding brc_yv_def x_last_def last_unit_x_def
    by simp
qed

lemma brc_yv_nonzero_elimination_witness_from_last_unit:
  assumes v_form: "𝗏 = 4 * w + 1"
  assumes abcd: "𝗄 - Λ = a^2 + b^2 + c^2 + d^2"
  assumes elim: "brc_elimination_witness a b c d (last_unit_x w) w"
  shows "∃a b c d x.
       𝗄 - Λ = a^2 + b^2 + c^2 + d^2 ∧
       brc_elimination_witness a b c d x w ∧
       brc_yv x w ≠ 0"
proof -
  have yv1: "brc_yv (last_unit_x w) w = 1"
    using last_unit_x_last[OF v_form] .
  then have nz: "brc_yv (last_unit_x w) w ≠ 0"
    by simp
  show ?thesis
    using abcd elim nz
    by blast
qed

lemma brc_elimination_witness_last_unit_conditional:
  assumes v_form: "𝗏 = 4 * w + 1"
  assumes abcd: "𝗄 - Λ = a^2 + b^2 + c^2 + d^2"
  assumes unit_elim:
    "(∑i∈{0..<4*w}. (brc_L (last_unit_x w) i)^2)
     =
     y_blocks_sqsum a b c d (last_unit_x w) w"
  shows "brc_elimination_witness a b c d (last_unit_x w) w"
  using unit_elim
  unfolding brc_elimination_witness_def
  by simp

lemma brc_local_linear_comb_last4:
  fixes a b c d :: nat
  fixes y0 y1 y2 y3 :: rat
  fixes x :: "rat mat"
  fixes m i :: nat
  assumes four_sq: "a^2 + b^2 + c^2 + d^2 = 𝗄 - Λ"
  assumes m_v: "m ≤ 𝗏"
  assumes m_gt3: "3 < m"
  assumes i4: "i ∈ {0..<4}"
  assumes x0_y:
    "x $$ (m-4,0) = one_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x1_y:
    "x $$ (m-3,0) = two_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x2_y:
    "x $$ (m-2,0) = three_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x3_y:
    "x $$ (m-1,0) = four_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  shows
    "∃e0 e1 e2 e3 :: rat.
      (∑h∈{0..<m}. of_int (N $$ (m-h-1,m-i-1)) * x $$ (m-h-1,0))
      =
      e0*y0 + e1*y1 + e2*y2 + e3*y3 +
      (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-i-1)) * x $$ (m-h-1,0))"
  using linear_comb_of_y_part_2[
    OF four_sq m_v m_gt3 i4
       refl refl refl refl
       x0_y x1_y x2_y x3_y]
  .

lemma brc_local_linear_comb_i0:
  fixes a b c d :: nat
  fixes y0 y1 y2 y3 :: rat
  fixes x :: "rat mat"
  fixes m :: nat
  assumes four_sq: "a^2 + b^2 + c^2 + d^2 = 𝗄 - Λ"
  assumes m_v: "m ≤ 𝗏"
  assumes m_gt3: "3 < m"
  assumes x0_y:
    "x $$ (m-4,0) = one_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x1_y:
    "x $$ (m-3,0) = two_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x2_y:
    "x $$ (m-2,0) = three_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x3_y:
    "x $$ (m-1,0) = four_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  shows
    "∃e0 e1 e2 e3 :: rat.
      (∑h∈{0..<m}. of_int (N $$ (m-h-1,m-1)) * x $$ (m-h-1,0))
      =
      e0*y0 + e1*y1 + e2*y2 + e3*y3 +
      (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-1)) * x $$ (m-h-1,0))"
proof -
  have i0: "0 ∈ {0..<4::nat}"
    by simp

  obtain e0 e1 e2 e3 :: rat where raw:
    "(∑h∈{0..<m}. of_int (N $$ (m-h-1,m-0-1)) * x $$ (m-h-1,0))
      =
      e0*y0 + e1*y1 + e2*y2 + e3*y3 +
      (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-0-1)) * x $$ (m-h-1,0))"
    using brc_local_linear_comb_last4[
      OF four_sq m_v m_gt3 i0 x0_y x1_y x2_y x3_y]
    by blast

  have clean:
    "(∑h∈{0..<m}. of_int (N $$ (m-h-1,m-1)) * x $$ (m-h-1,0))
      =
      e0*y0 + e1*y1 + e2*y2 + e3*y3 +
      (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-1)) * x $$ (m-h-1,0))"
    using raw by simp

  show ?thesis
    using clean by blast
qed

lemma brc_local_linear_comb_i1:
  fixes a b c d :: nat
  fixes y0 y1 y2 y3 :: rat
  fixes x :: "rat mat"
  fixes m :: nat
  assumes four_sq: "a^2 + b^2 + c^2 + d^2 = 𝗄 - Λ"
  assumes m_v: "m ≤ 𝗏"
  assumes m_gt3: "3 < m"
  assumes x0_y:
    "x $$ (m-4,0) = one_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x1_y:
    "x $$ (m-3,0) = two_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x2_y:
    "x $$ (m-2,0) = three_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x3_y:
    "x $$ (m-1,0) = four_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  shows
    "∃e0 e1 e2 e3 :: rat.
      (∑h∈{0..<m}. of_int (N $$ (m-h-1,m - Suc (Suc 0))) * x $$ (m-h-1,0))
      =
      e0*y0 + e1*y1 + e2*y2 + e3*y3 +
      (∑h∈{4..<m}. of_int (N $$ (m-h-1,m - Suc (Suc 0))) * x $$ (m-h-1,0))"
proof -
  have i1: "1 ∈ {0..<4::nat}"
    by simp

  obtain e0 e1 e2 e3 :: rat where raw:
    "(∑h∈{0..<m}. of_int (N $$ (m-h-1,m-1-1)) * x $$ (m-h-1,0))
      =
      e0*y0 + e1*y1 + e2*y2 + e3*y3 +
      (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-1-1)) * x $$ (m-h-1,0))"
    using brc_local_linear_comb_last4[
      OF four_sq m_v m_gt3 i1 x0_y x1_y x2_y x3_y]
    by blast

  show ?thesis
  proof -
    have
      "(∑h∈{0..<m}. of_int (N $$ (m-h-1,m - Suc (Suc 0))) * x $$ (m-h-1,0))
      =
      e0*y0 + e1*y1 + e2*y2 + e3*y3 +
      (∑h∈{4..<m}. of_int (N $$ (m-h-1,m - Suc (Suc 0))) * x $$ (m-h-1,0))"
      using raw by simp
    then show ?thesis
      by blast
  qed
qed

lemma brc_local_linear_comb_i2:
  fixes a b c d :: nat
  fixes y0 y1 y2 y3 :: rat
  fixes x :: "rat mat"
  fixes m :: nat
  assumes four_sq: "a^2 + b^2 + c^2 + d^2 = 𝗄 - Λ"
  assumes m_v: "m ≤ 𝗏"
  assumes m_gt3: "3 < m"
  assumes x0_y:
    "x $$ (m-4,0) = one_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x1_y:
    "x $$ (m-3,0) = two_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x2_y:
    "x $$ (m-2,0) = three_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x3_y:
    "x $$ (m-1,0) = four_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  shows
    "∃e0 e1 e2 e3 :: rat.
      (∑h∈{0..<m}. of_int (N $$ (m-h-1,m-3)) * x $$ (m-h-1,0))
      =
      e0*y0 + e1*y1 + e2*y2 + e3*y3 +
      (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-3)) * x $$ (m-h-1,0))"
proof -
  have i2: "2 ∈ {0..<4::nat}"
    by simp

  obtain e0 e1 e2 e3 :: rat where raw:
    "(∑h∈{0..<m}. of_int (N $$ (m-h-1,m-2-1)) * x $$ (m-h-1,0))
      =
      e0*y0 + e1*y1 + e2*y2 + e3*y3 +
      (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-2-1)) * x $$ (m-h-1,0))"
    using brc_local_linear_comb_last4[
      OF four_sq m_v m_gt3 i2 x0_y x1_y x2_y x3_y]
    by blast

  have target:
    "(∑h∈{0..<m}. of_int (N $$ (m-h-1,m-3)) * x $$ (m-h-1,0))
      =
      e0*y0 + e1*y1 + e2*y2 + e3*y3 +
      (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-3)) * x $$ (m-h-1,0))"
    using raw by simp

  show ?thesis
    using target by blast
qed

lemma brc_local_linear_comb_i3:
  fixes a b c d :: nat
  fixes y0 y1 y2 y3 :: rat
  fixes x :: "rat mat"
  fixes m :: nat
  assumes four_sq: "a^2 + b^2 + c^2 + d^2 = 𝗄 - Λ"
  assumes m_v: "m ≤ 𝗏"
  assumes m_gt3: "3 < m"
  assumes x0_y:
    "x $$ (m-4,0) = one_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x1_y:
    "x $$ (m-3,0) = two_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x2_y:
    "x $$ (m-2,0) = three_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x3_y:
    "x $$ (m-1,0) = four_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  shows
    "∃e0 e1 e2 e3 :: rat.
      (∑h∈{0..<m}. of_int (N $$ (m-h-1,m-4)) * x $$ (m-h-1,0))
      =
      e0*y0 + e1*y1 + e2*y2 + e3*y3 +
      (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-4)) * x $$ (m-h-1,0))"
proof -
  have i3: "3 ∈ {0..<4::nat}"
    by simp

  obtain e0 e1 e2 e3 :: rat where raw:
    "(∑h∈{0..<m}. of_int (N $$ (m-h-1,m-3-1)) * x $$ (m-h-1,0))
      =
      e0*y0 + e1*y1 + e2*y2 + e3*y3 +
      (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-3-1)) * x $$ (m-h-1,0))"
    using brc_local_linear_comb_last4[
      OF four_sq m_v m_gt3 i3 x0_y x1_y x2_y x3_y]
    by blast

  have target:
    "(∑h∈{0..<m}. of_int (N $$ (m-h-1,m-4)) * x $$ (m-h-1,0))
      =
      e0*y0 + e1*y1 + e2*y2 + e3*y3 +
      (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-4)) * x $$ (m-h-1,0))"
    using raw by simp

  show ?thesis
    using target by blast
qed

lemma brc_local_linear_comb_four_exists:
  fixes a b c d :: nat
  fixes y0 y1 y2 y3 :: rat
  fixes x :: "rat mat"
  fixes m :: nat
  assumes four_sq: "a^2 + b^2 + c^2 + d^2 = 𝗄 - Λ"
  assumes m_v: "m ≤ 𝗏"
  assumes m_gt3: "3 < m"
  assumes x0_y:
    "x $$ (m-4,0) = one_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x1_y:
    "x $$ (m-3,0) = two_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x2_y:
    "x $$ (m-2,0) = three_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x3_y:
    "x $$ (m-1,0) = four_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  shows
    "∃A0 A1 A2 A3 R0 R1 R2 R3 :: rat.
      (∑h∈{0..<m}. of_int (N $$ (m-h-1,m-1)) * x $$ (m-h-1,0))
        = A0*y0 + R0 ∧
      (∑h∈{0..<m}. of_int (N $$ (m-h-1,m - Suc (Suc 0))) * x $$ (m-h-1,0))
        = A1*y1 + R1 ∧
      (∑h∈{0..<m}. of_int (N $$ (m-h-1,m-3)) * x $$ (m-h-1,0))
        = A2*y2 + R2 ∧
      (∑h∈{0..<m}. of_int (N $$ (m-h-1,m-4)) * x $$ (m-h-1,0))
        = A3*y3 + R3"
proof -
  obtain e00 e01 e02 e03 :: rat where eq0:
    "(∑h∈{0..<m}. of_int (N $$ (m-h-1,m-1)) * x $$ (m-h-1,0))
      =
      e00*y0 + e01*y1 + e02*y2 + e03*y3 +
      (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-1)) * x $$ (m-h-1,0))"
    using brc_local_linear_comb_i0[
      OF four_sq m_v m_gt3 x0_y x1_y x2_y x3_y]
    by blast

  obtain e10 e11 e12 e13 :: rat where eq1:
    "(∑h∈{0..<m}. of_int (N $$ (m-h-1,m - Suc (Suc 0))) * x $$ (m-h-1,0))
      =
      e10*y0 + e11*y1 + e12*y2 + e13*y3 +
      (∑h∈{4..<m}. of_int (N $$ (m-h-1,m - Suc (Suc 0))) * x $$ (m-h-1,0))"
    using brc_local_linear_comb_i1[
      OF four_sq m_v m_gt3 x0_y x1_y x2_y x3_y]
    by blast

  obtain e20 e21 e22 e23 :: rat where eq2:
    "(∑h∈{0..<m}. of_int (N $$ (m-h-1,m-3)) * x $$ (m-h-1,0))
      =
      e20*y0 + e21*y1 + e22*y2 + e23*y3 +
      (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-3)) * x $$ (m-h-1,0))"
    using brc_local_linear_comb_i2[
      OF four_sq m_v m_gt3 x0_y x1_y x2_y x3_y]
    by blast

  obtain e30 e31 e32 e33 :: rat where eq3:
    "(∑h∈{0..<m}. of_int (N $$ (m-h-1,m-4)) * x $$ (m-h-1,0))
      =
      e30*y0 + e31*y1 + e32*y2 + e33*y3 +
      (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-4)) * x $$ (m-h-1,0))"
    using brc_local_linear_comb_i3[
      OF four_sq m_v m_gt3 x0_y x1_y x2_y x3_y]
    by blast

  let ?R0 = "e01*y1 + e02*y2 + e03*y3 +
      (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-1)) * x $$ (m-h-1,0))"
  let ?R1 = "e10*y0 + e12*y2 + e13*y3 +
      (∑h∈{4..<m}. of_int (N $$ (m-h-1,m - Suc (Suc 0))) * x $$ (m-h-1,0))"
  let ?R2 = "e20*y0 + e21*y1 + e23*y3 +
      (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-3)) * x $$ (m-h-1,0))"
  let ?R3 = "e30*y0 + e31*y1 + e32*y2 +
      (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-4)) * x $$ (m-h-1,0))"

  show ?thesis
  proof
    show "∃A1 A2 A3 R0 R1 R2 R3 :: rat.
      (∑h∈{0..<m}. of_int (N $$ (m-h-1,m-1)) * x $$ (m-h-1,0))
        = e00*y0 + R0 ∧
      (∑h∈{0..<m}. of_int (N $$ (m-h-1,m - Suc (Suc 0))) * x $$ (m-h-1,0))
        = A1*y1 + R1 ∧
      (∑h∈{0..<m}. of_int (N $$ (m-h-1,m-3)) * x $$ (m-h-1,0))
        = A2*y2 + R2 ∧
      (∑h∈{0..<m}. of_int (N $$ (m-h-1,m-4)) * x $$ (m-h-1,0))
        = A3*y3 + R3"
    proof
      show "∃A2 A3 R0 R1 R2 R3 :: rat.
        (∑h∈{0..<m}. of_int (N $$ (m-h-1,m-1)) * x $$ (m-h-1,0))
          = e00*y0 + R0 ∧
        (∑h∈{0..<m}. of_int (N $$ (m-h-1,m - Suc (Suc 0))) * x $$ (m-h-1,0))
          = e11*y1 + R1 ∧
        (∑h∈{0..<m}. of_int (N $$ (m-h-1,m-3)) * x $$ (m-h-1,0))
          = A2*y2 + R2 ∧
        (∑h∈{0..<m}. of_int (N $$ (m-h-1,m-4)) * x $$ (m-h-1,0))
          = A3*y3 + R3"
      proof
        show "∃A3 R0 R1 R2 R3 :: rat.
          (∑h∈{0..<m}. of_int (N $$ (m-h-1,m-1)) * x $$ (m-h-1,0))
            = e00*y0 + R0 ∧
          (∑h∈{0..<m}. of_int (N $$ (m-h-1,m - Suc (Suc 0))) * x $$ (m-h-1,0))
            = e11*y1 + R1 ∧
          (∑h∈{0..<m}. of_int (N $$ (m-h-1,m-3)) * x $$ (m-h-1,0))
            = e22*y2 + R2 ∧
          (∑h∈{0..<m}. of_int (N $$ (m-h-1,m-4)) * x $$ (m-h-1,0))
            = A3*y3 + R3"
        proof
          show "∃R0 R1 R2 R3 :: rat.
            (∑h∈{0..<m}. of_int (N $$ (m-h-1,m-1)) * x $$ (m-h-1,0))
              = e00*y0 + R0 ∧
            (∑h∈{0..<m}. of_int (N $$ (m-h-1,m - Suc (Suc 0))) * x $$ (m-h-1,0))
              = e11*y1 + R1 ∧
            (∑h∈{0..<m}. of_int (N $$ (m-h-1,m-3)) * x $$ (m-h-1,0))
              = e22*y2 + R2 ∧
            (∑h∈{0..<m}. of_int (N $$ (m-h-1,m-4)) * x $$ (m-h-1,0))
              = e33*y3 + R3"
          proof
            show "∃R1 R2 R3 :: rat.
              (∑h∈{0..<m}. of_int (N $$ (m-h-1,m-1)) * x $$ (m-h-1,0))
                = e00*y0 + ?R0 ∧
              (∑h∈{0..<m}. of_int (N $$ (m-h-1,m - Suc (Suc 0))) * x $$ (m-h-1,0))
                = e11*y1 + R1 ∧
              (∑h∈{0..<m}. of_int (N $$ (m-h-1,m-3)) * x $$ (m-h-1,0))
                = e22*y2 + R2 ∧
              (∑h∈{0..<m}. of_int (N $$ (m-h-1,m-4)) * x $$ (m-h-1,0))
                = e33*y3 + R3"
            proof
              show "∃R2 R3 :: rat.
                (∑h∈{0..<m}. of_int (N $$ (m-h-1,m-1)) * x $$ (m-h-1,0))
                  = e00*y0 + ?R0 ∧
                (∑h∈{0..<m}. of_int (N $$ (m-h-1,m - Suc (Suc 0))) * x $$ (m-h-1,0))
                  = e11*y1 + ?R1 ∧
                (∑h∈{0..<m}. of_int (N $$ (m-h-1,m-3)) * x $$ (m-h-1,0))
                  = e22*y2 + R2 ∧
                (∑h∈{0..<m}. of_int (N $$ (m-h-1,m-4)) * x $$ (m-h-1,0))
                  = e33*y3 + R3"
              proof
                show "∃R3 :: rat.
                  (∑h∈{0..<m}. of_int (N $$ (m-h-1,m-1)) * x $$ (m-h-1,0))
                    = e00*y0 + ?R0 ∧
                  (∑h∈{0..<m}. of_int (N $$ (m-h-1,m - Suc (Suc 0))) * x $$ (m-h-1,0))
                    = e11*y1 + ?R1 ∧
                  (∑h∈{0..<m}. of_int (N $$ (m-h-1,m-3)) * x $$ (m-h-1,0))
                    = e22*y2 + ?R2 ∧
                  (∑h∈{0..<m}. of_int (N $$ (m-h-1,m-4)) * x $$ (m-h-1,0))
                    = e33*y3 + R3"
                proof
                  show
                    "(∑h∈{0..<m}. of_int (N $$ (m-h-1,m-1)) * x $$ (m-h-1,0))
                      = e00*y0 + ?R0 ∧
                    (∑h∈{0..<m}. of_int (N $$ (m-h-1,m - Suc (Suc 0))) * x $$ (m-h-1,0))
                      = e11*y1 + ?R1 ∧
                    (∑h∈{0..<m}. of_int (N $$ (m-h-1,m-3)) * x $$ (m-h-1,0))
                      = e22*y2 + ?R2 ∧
                    (∑h∈{0..<m}. of_int (N $$ (m-h-1,m-4)) * x $$ (m-h-1,0))
                      = e33*y3 + ?R3"
                    using eq0 eq1 eq2 eq3
                    by (simp add: algebra_simps)
                qed
              qed
            qed
          qed
        qed
      qed
    qed
  qed
qed

lemma brc_choose_local_y_block:
  fixes A0 A1 A2 A3 R0 R1 R2 R3 :: rat
  shows
    "∃y0 y1 y2 y3 :: rat.
        (A0*y0 + R0)^2 +
        (A1*y1 + R1)^2 +
        (A2*y2 + R2)^2 +
        (A3*y3 + R3)^2
        =
        y0^2 + y1^2 + y2^2 + y3^2"
proof -
  obtain y0 where y0: "(A0*y0 + R0)^2 = y0^2"
    using choose_y_square_cancel[of A0 R0] by blast
  obtain y1 where y1: "(A1*y1 + R1)^2 = y1^2"
    using choose_y_square_cancel[of A1 R1] by blast
  obtain y2 where y2: "(A2*y2 + R2)^2 = y2^2"
    using choose_y_square_cancel[of A2 R2] by blast
  obtain y3 where y3: "(A3*y3 + R3)^2 = y3^2"
    using choose_y_square_cancel[of A3 R3] by blast

  show ?thesis
  proof
    show "∃y1 y2 y3.
      (A0*y0 + R0)^2 + (A1*y1 + R1)^2 +
      (A2*y2 + R2)^2 + (A3*y3 + R3)^2 =
      y0^2 + y1^2 + y2^2 + y3^2"
    proof
      show "∃y2 y3.
        (A0*y0 + R0)^2 + (A1*y1 + R1)^2 +
        (A2*y2 + R2)^2 + (A3*y3 + R3)^2 =
        y0^2 + y1^2 + y2^2 + y3^2"
      proof
        show "∃y3.
          (A0*y0 + R0)^2 + (A1*y1 + R1)^2 +
          (A2*y2 + R2)^2 + (A3*y3 + R3)^2 =
          y0^2 + y1^2 + y2^2 + y3^2"
        proof
          show "(A0*y0 + R0)^2 + (A1*y1 + R1)^2 +
                (A2*y2 + R2)^2 + (A3*y3 + R3)^2 =
                y0^2 + y1^2 + y2^2 + y3^2"
            using y0 y1 y2 y3
            by simp
        qed
      qed
    qed
  qed
qed

definition update_x_block ::
  "rat mat ⇒ nat ⇒ rat ⇒ rat ⇒ rat ⇒ rat ⇒ rat mat" where
  "update_x_block x h x0 x1 x2 x3 =
     mat 𝗏 1
       (λ(i,j).
          if j = 0 ∧ i = 4*h then x0
          else if j = 0 ∧ i = 4*h + 1 then x1
          else if j = 0 ∧ i = 4*h + 2 then x2
          else if j = 0 ∧ i = 4*h + 3 then x3
          else x $$ (i,j))"

lemma update_x_block_0:
  assumes "4*h < 𝗏"
  shows "update_x_block x h x0 x1 x2 x3 $$ (4*h,0) = x0"
  unfolding update_x_block_def
  using assms by simp

lemma update_x_block_1:
  assumes "4*h + 1 < 𝗏"
  shows "update_x_block x h x0 x1 x2 x3 $$ (4*h + 1,0) = x1"
  unfolding update_x_block_def
  using assms by simp

lemma update_x_block_2:
  assumes "4*h + 2 < 𝗏"
  shows "update_x_block x h x0 x1 x2 x3 $$ (4*h + 2,0) = x2"
  unfolding update_x_block_def
  using assms by simp

lemma update_x_block_3:
  assumes "4*h + 3 < 𝗏"
  shows "update_x_block x h x0 x1 x2 x3 $$ (4*h + 3,0) = x3"
  unfolding update_x_block_def
  using assms by simp

lemma update_x_block_preserve_after:
  assumes i_ge: "4 * Suc h ≤ i"
  assumes i_lt: "i < 𝗏"
  shows "update_x_block x h x0 x1 x2 x3 $$ (i,0) = x $$ (i,0)"
proof -
  have neq0: "i ≠ 4*h"
    using i_ge by auto
  have neq1: "i ≠ 4*h + 1"
    using i_ge by auto
  have neq2: "i ≠ 4*h + 2"
    using i_ge by auto
  have neq3: "i ≠ 4*h + 3"
    using i_ge by auto
  show ?thesis
    unfolding update_x_block_def
    using i_lt neq0 neq1 neq2 neq3
    by simp
qed

lemma update_x_block_preserve_before:
  assumes i_lt_block: "i < 4*h"
  assumes i_lt: "i < 𝗏"
  shows "update_x_block x h x0 x1 x2 x3 $$ (i,0) = x $$ (i,0)"
proof -
  have neq0: "i ≠ 4*h"
    using i_lt_block by auto
  have neq1: "i ≠ 4*h + 1"
    using i_lt_block by auto
  have neq2: "i ≠ 4*h + 2"
    using i_lt_block by auto
  have neq3: "i ≠ 4*h + 3"
    using i_lt_block by auto
  show ?thesis
    unfolding update_x_block_def
    using i_lt neq0 neq1 neq2 neq3
    by simp
qed

lemma update_x_block_y_inv_entries:
  fixes a b c d :: nat
  fixes y0 y1 y2 y3 :: rat
  assumes nzsum: "a^2 + b^2 + c^2 + d^2 ≠ 0"
  assumes b0: "4*h < 𝗏"
  assumes b1: "4*h + 1 < 𝗏"
  assumes b2: "4*h + 2 < 𝗏"
  assumes b3: "4*h + 3 < 𝗏"
  defines "x0 ≡ one_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  defines "x1 ≡ two_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  defines "x2 ≡ three_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  defines "x3 ≡ four_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  shows
    "y_of ((a,b,c,d),
      (update_x_block x h x0 x1 x2 x3 $$ (4*h,0),
       update_x_block x h x0 x1 x2 x3 $$ (4*h+1,0),
       update_x_block x h x0 x1 x2 x3 $$ (4*h+2,0),
       update_x_block x h x0 x1 x2 x3 $$ (4*h+3,0)))
     = (y0,y1,y2,y3)"
proof -
  have entries:
    "update_x_block x h x0 x1 x2 x3 $$ (4*h,0) = x0"
    "update_x_block x h x0 x1 x2 x3 $$ (4*h+1,0) = x1"
    "update_x_block x h x0 x1 x2 x3 $$ (4*h+2,0) = x2"
    "update_x_block x h x0 x1 x2 x3 $$ (4*h+3,0) = x3"
    using update_x_block_0[OF b0, of x x0 x1 x2 x3]
          update_x_block_1[OF b1, of x x0 x1 x2 x3]
          update_x_block_2[OF b2, of x x0 x1 x2 x3]
          update_x_block_3[OF b3, of x x0 x1 x2 x3]
    by simp_all

  have inv:
    "y_reversible (y_inv_reversible ((a,b,c,d),(y0,y1,y2,y3)))
     = ((a,b,c,d),(y0,y1,y2,y3))"
    using y_inverses_part_2[OF nzsum, of y0 y1 y2 y3] .

  show ?thesis
    using entries inv
    unfolding x0_def x1_def x2_def x3_def
    by simp
qed

lemma y_block_sqsum_update_y_inv:
  fixes a b c d :: nat
  fixes y0 y1 y2 y3 :: rat
  assumes nzsum: "a^2 + b^2 + c^2 + d^2 ≠ 0"
  assumes b0: "4*h < 𝗏"
  assumes b1: "4*h + 1 < 𝗏"
  assumes b2: "4*h + 2 < 𝗏"
  assumes b3: "4*h + 3 < 𝗏"
  defines "x0 ≡ one_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  defines "x1 ≡ two_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  defines "x2 ≡ three_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  defines "x3 ≡ four_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  shows
    "y_block_sqsum a b c d
       (update_x_block x h x0 x1 x2 x3) h
     =
     y0^2 + y1^2 + y2^2 + y3^2"
proof -
  have yblock:
    "y_of ((a,b,c,d),
      (update_x_block x h x0 x1 x2 x3 $$ (4*h,0),
       update_x_block x h x0 x1 x2 x3 $$ (4*h+1,0),
       update_x_block x h x0 x1 x2 x3 $$ (4*h+2,0),
       update_x_block x h x0 x1 x2 x3 $$ (4*h+3,0)))
     = (y0,y1,y2,y3)"
  proof -
    have e0:
      "update_x_block x h x0 x1 x2 x3 $$ (4*h,0) =
       one_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
      using update_x_block_0[OF b0, of x x0 x1 x2 x3]
      unfolding x0_def by simp
    have e1:
      "update_x_block x h x0 x1 x2 x3 $$ (4*h+1,0) =
       two_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
      using update_x_block_1[OF b1, of x x0 x1 x2 x3]
      unfolding x1_def by simp
    have e2:
      "update_x_block x h x0 x1 x2 x3 $$ (4*h+2,0) =
       three_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
      using update_x_block_2[OF b2, of x x0 x1 x2 x3]
      unfolding x2_def by simp
    have e3:
      "update_x_block x h x0 x1 x2 x3 $$ (4*h+3,0) =
       four_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
      using update_x_block_3[OF b3, of x x0 x1 x2 x3]
      unfolding x3_def by simp

    have inv:
      "y_reversible (y_inv_reversible ((a,b,c,d),(y0,y1,y2,y3)))
       = ((a,b,c,d),(y0,y1,y2,y3))"
      using y_inverses_part_2[OF nzsum, of y0 y1 y2 y3] .

    show ?thesis
      using e0 e1 e2 e3 inv
      by simp
  qed

  show ?thesis
    unfolding y_block_sqsum_def
    using yblock
    by simp
qed

lemma y_block_sqsum_update_from_chosen_y:
  fixes a b c d :: nat
  fixes y0 y1 y2 y3 :: rat
  assumes nzsum: "a^2 + b^2 + c^2 + d^2 ≠ 0"
  assumes b0: "4*h < 𝗏"
  assumes b1: "4*h + 1 < 𝗏"
  assumes b2: "4*h + 2 < 𝗏"
  assumes b3: "4*h + 3 < 𝗏"
  shows
    "∃x0 x1 x2 x3 :: rat.
       y_block_sqsum a b c d
         (update_x_block x h x0 x1 x2 x3) h
       =
       y0^2 + y1^2 + y2^2 + y3^2"
proof -
  let ?x0 = "one_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  let ?x1 = "two_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  let ?x2 = "three_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  let ?x3 = "four_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"

  have eq:
    "y_block_sqsum a b c d
       (update_x_block x h ?x0 ?x1 ?x2 ?x3) h
     =
     y0^2 + y1^2 + y2^2 + y3^2"
    using y_block_sqsum_update_y_inv[
      OF nzsum b0 b1 b2 b3, of x y0 y1 y2 y3]
    by simp

  show ?thesis
    using eq by blast
qed

lemma brc_local_updated_block_linear_forms:
  fixes a b c d :: nat
  fixes y0 y1 y2 y3 :: rat
  fixes x :: "rat mat"
  fixes m :: nat
  assumes four_sq: "a^2 + b^2 + c^2 + d^2 = 𝗄 - Λ"
  assumes nzsum: "a^2 + b^2 + c^2 + d^2 ≠ 0"
  assumes m_v: "m ≤ 𝗏"
  assumes m_gt3: "3 < m"
  assumes m_block: "m = 4 * Suc h"
  assumes b0: "4*h < 𝗏"
  assumes b1: "4*h + 1 < 𝗏"
  assumes b2: "4*h + 2 < 𝗏"
  assumes b3: "4*h + 3 < 𝗏"
  defines "x0 ≡ one_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  defines "x1 ≡ two_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  defines "x2 ≡ three_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  defines "x3 ≡ four_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  shows
    "∃A0 A1 A2 A3 R0 R1 R2 R3 :: rat.
      (∑j∈{0..<m}. of_int (N $$ (m-j-1,m-1)) *
          (update_x_block x h x0 x1 x2 x3) $$ (m-j-1,0))
        = A0*y0 + R0 ∧
      (∑j∈{0..<m}. of_int (N $$ (m-j-1,m - Suc (Suc 0))) *
          (update_x_block x h x0 x1 x2 x3) $$ (m-j-1,0))
        = A1*y1 + R1 ∧
      (∑j∈{0..<m}. of_int (N $$ (m-j-1,m-3)) *
          (update_x_block x h x0 x1 x2 x3) $$ (m-j-1,0))
        = A2*y2 + R2 ∧
      (∑j∈{0..<m}. of_int (N $$ (m-j-1,m-4)) *
          (update_x_block x h x0 x1 x2 x3) $$ (m-j-1,0))
        = A3*y3 + R3"
proof -
  have e0:
    "(update_x_block x h x0 x1 x2 x3) $$ (m-4,0)
     = one_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
    using update_x_block_0[OF b0, of x x0 x1 x2 x3]
    unfolding x0_def m_block
    by simp

  have e1:
    "(update_x_block x h x0 x1 x2 x3) $$ (m-3,0)
     = two_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
    using update_x_block_1[OF b1, of x x0 x1 x2 x3]
    unfolding x1_def m_block
    by simp

  have e2:
    "(update_x_block x h x0 x1 x2 x3) $$ (m-2,0)
     = three_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
    using update_x_block_2[OF b2, of x x0 x1 x2 x3]
    unfolding x2_def m_block
    by simp

  have e3:
    "(update_x_block x h x0 x1 x2 x3) $$ (m-1,0)
     = four_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
    using update_x_block_3[OF b3, of x x0 x1 x2 x3]
    unfolding x3_def m_block
    by (simp add: add.commute)

  show ?thesis
    using brc_local_linear_comb_four_exists[
      OF four_sq m_v m_gt3 e0 e1 e2 e3]
    .
qed

lemma brc_local_block_update_exists:
  fixes a b c d :: nat
  fixes x :: "rat mat"
  fixes h :: nat
  assumes nzsum: "a^2 + b^2 + c^2 + d^2 ≠ 0"
  assumes b0: "4*h < 𝗏"
  assumes b1: "4*h + 1 < 𝗏"
  assumes b2: "4*h + 2 < 𝗏"
  assumes b3: "4*h + 3 < 𝗏"
  shows "∃x' y0 y1 y2 y3.
      y_block_sqsum a b c d x' h =
      y0^2 + y1^2 + y2^2 + y3^2"
proof -
  obtain y0 y1 y2 y3 :: rat where True
    by simp

  obtain x0 x1 x2 x3 :: rat where rhs:
    "y_block_sqsum a b c d
       (update_x_block x h x0 x1 x2 x3) h
     =
     y0^2 + y1^2 + y2^2 + y3^2"
    using y_block_sqsum_update_from_chosen_y[
      OF nzsum b0 b1 b2 b3, of x y0 y1 y2 y3]
    by blast

  then show ?thesis
    by blast
qed

definition brc_start_x :: "nat ⇒ rat mat" where
  "brc_start_x w =
     mat 𝗏 1 (λ(i,j). if j = 0 ∧ i = 4*w then 1 else 0)"

lemma brc_start_x_yv_nonzero:
  assumes v_form: "𝗏 = 4 * w + 1"
  shows "brc_yv (brc_start_x w) w ≠ 0"
proof -
  have "4*w < 𝗏"
    using v_form by simp
  then have "brc_yv (brc_start_x w) w = 1"
    unfolding brc_yv_def x_last_def brc_start_x_def
    by simp
  then show ?thesis
    by simp
qed

lemma last_unit_x_yv_nonzero:
  assumes v_form: "𝗏 = 4 * w + 1"
  shows "brc_yv (last_unit_x w) w ≠ 0"
  using last_unit_x_last[OF v_form]
  by simp

lemma brc_yv_preserved_by_tail_preserve:
  assumes v_form: "𝗏 = 4 * w + 1"
  assumes h_lt: "h < w"
  assumes preserve:
    "∀i. 4 * Suc h ≤ i ⟶ i < 𝗏 ⟶ x' $$ (i,0) = x $$ (i,0)"
  shows "brc_yv x' w = brc_yv x w"
proof -
  have idx_ge: "4 * Suc h ≤ 4 * w"
    using h_lt by simp
  have idx_lt: "4 * w < 𝗏"
    using v_form by simp
  have "x' $$ (4*w,0) = x $$ (4*w,0)"
    using preserve idx_ge idx_lt by blast
  then show ?thesis
    unfolding brc_yv_def x_last_def
    by simp
qed

lemma brc_apply_local_step_preserves_yv:
  assumes v_form: "𝗏 = 4 * w + 1"
  assumes h_lt: "h < w"
  assumes four_sq: "a^2 + b^2 + c^2 + d^2 = 𝗄 - Λ"
  assumes nzsum: "a^2 + b^2 + c^2 + d^2 ≠ 0"
  assumes local_step:
    "⋀x h m.
      m ≤ 𝗏 ⟹
      3 < m ⟹
      m = 4 * Suc h ⟹
      4*h < 𝗏 ⟹
      4*h + 1 < 𝗏 ⟹
      4*h + 2 < 𝗏 ⟹
      4*h + 3 < 𝗏 ⟹
      ∃x'.
        (∀i. 4 * Suc h ≤ i ⟶ i < 𝗏 ⟶ x' $$ (i,0) = x $$ (i,0)) ∧
        y_block_sqsum a b c d x' h =
          (∑j∈{0..<4}.
            (∑r∈{0..<4 * Suc h}.
              of_int (N $$ (4 * Suc h-r-1,4 * Suc h-j-1)) *
              x' $$ (4 * Suc h-r-1,0))^2)"
  shows "∃x'. brc_yv x' w = brc_yv x w"
proof -
  let ?m = "4 * Suc h"

  have m_v: "?m ≤ 𝗏"
    using h_lt v_form by simp
  have m_gt3: "3 < ?m"
    by simp
  have b0: "4*h < 𝗏"
    using h_lt v_form by simp
  have b1: "4*h + 1 < 𝗏"
    using h_lt v_form by simp
  have b2: "4*h + 2 < 𝗏"
    using h_lt v_form by simp
  have b3: "4*h + 3 < 𝗏"
    using h_lt v_form by simp

  obtain x' where preserve:
    "∀i. 4 * Suc h ≤ i ⟶ i < 𝗏 ⟶ x' $$ (i,0) = x $$ (i,0)"
    using local_step[OF m_v m_gt3 refl b0 b1 b2 b3]
    by blast

  have "brc_yv x' w = brc_yv x w"
    using brc_yv_preserved_by_tail_preserve[OF v_form h_lt preserve] .

  then show ?thesis
    by blast
qed

definition brc_prefix_eliminated ::
  "nat ⇒ nat ⇒ nat ⇒ nat ⇒ rat mat ⇒ nat ⇒ bool" where
  "brc_prefix_eliminated a b c d x q ⟷
     (∀t. t < q ⟶
        y_block_sqsum a b c d x t =
        (∑j∈{0..<4}.
          (∑r∈{0..<4 * Suc t}.
            of_int (N $$ (4 * Suc t-r-1,4 * Suc t-j-1)) *
            x $$ (4 * Suc t-r-1,0))^2))"

definition brc_prefix_good ::
  "nat ⇒ nat ⇒ nat ⇒ nat ⇒ rat mat ⇒ nat ⇒ nat ⇒ bool" where
  "brc_prefix_good a b c d x q w ⟷
     brc_prefix_eliminated a b c d x q ∧
     (∀h j. h < q ⟶ j < 4 ⟶
        (∑r∈{4 * Suc h..<𝗏}.
          of_int (N $$ (r, 4*h+j)) * x $$ (r,0)) = 0)"

lemma brc_prefix_good_base:
  "brc_prefix_good a b c d x 0 w"
  unfolding brc_prefix_good_def brc_prefix_eliminated_def
  by simp

lemma brc_prefix_eliminated_base:
  "brc_prefix_eliminated a b c d x 0"
  unfolding brc_prefix_eliminated_def
  by simp

lemma brc_prefix_sum_blocks:
  assumes prefix: "brc_prefix_eliminated a b c d x w"
  shows
    "(∑h∈{0..<w}. y_block_sqsum a b c d x h)
     =
     (∑h∈{0..<w}.
        (∑j∈{0..<4}.
          (∑r∈{0..<4 * Suc h}.
            of_int (N $$ (4 * Suc h-r-1,4 * Suc h-j-1)) *
            x $$ (4 * Suc h-r-1,0))^2))"
  using prefix
  unfolding brc_prefix_eliminated_def
  by simp

definition brc_minus_equation :: bool where
  "brc_minus_equation ⟷
    (∃x y z :: rat.
      (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧
      x^2 = of_nat (𝗄 - Λ) * y^2 - of_nat Λ * z^2)"

lemma brc_minus_from_terminal:
  fixes xv1 y0 yv1 :: rat
  assumes terminal:
    "of_nat (𝗄 - Λ) * xv1^2 =
       of_nat Λ * y0^2 + yv1^2"
  assumes nonzero:
    "xv1 ≠ 0 ∨ y0 ≠ 0 ∨ yv1 ≠ 0"
  shows "brc_minus_equation"
proof -
  have eq:
    "yv1^2 =
       of_nat (𝗄 - Λ) * xv1^2 -
       of_nat Λ * y0^2"
    using terminal
    by linarith

  show ?thesis
    unfolding brc_minus_equation_def
  proof -
    show "∃x y z :: rat.
      (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧
      x^2 = of_nat (𝗄 - Λ) * y^2 - of_nat Λ * z^2"
      using eq nonzero
      by blast
  qed
qed

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

definition brc_minus_prefix_eliminated ::
  "nat ⇒ nat ⇒ nat ⇒ nat ⇒ rat mat ⇒ rat ⇒ nat ⇒ bool" where
  "brc_minus_prefix_eliminated a b c d x xv1 q ⟷
     (∀t. t < q ⟶
        y_block_sqsum a b c d (brc_extend_x x xv1) t =
        (∑j∈{0..<4}.
          (∑r∈{0..<4 * Suc t}.
            of_int
              (N $$ (4 * Suc t-r-1,
                      4 * Suc t-j-1)) *
            brc_extend_x x xv1 $$ (4 * Suc t-r-1,0))^2))"

definition brc_minus_prefix_good ::
  "nat ⇒ nat ⇒ nat ⇒ nat ⇒ rat mat ⇒ rat ⇒ nat ⇒ bool" where
  "brc_minus_prefix_good a b c d x xv1 q ⟷
     brc_minus_prefix_eliminated a b c d x xv1 q ∧
     (∀h j. h < q ⟶ j < 4 ⟶
        (∑r∈{4 * Suc h..<𝗏}.
          of_int (N $$ (r,4*h+j)) * x $$ (r,0)) = 0)"

lemma brc_minus_prefix_eliminated_base:
  "brc_minus_prefix_eliminated a b c d x xv1 0"
  unfolding brc_minus_prefix_eliminated_def
  by simp

lemma brc_minus_prefix_good_base:
  "brc_minus_prefix_good a b c d x xv1 0"
  unfolding brc_minus_prefix_good_def
  using brc_minus_prefix_eliminated_base
  by simp

lemma brc_minus_prefix_sum_blocks:
  assumes prefix:
    "brc_minus_prefix_eliminated a b c d x xv1 q"
  shows
    "(∑h∈{0..<q}.
        y_block_sqsum a b c d
          (brc_extend_x x xv1) h)
     =
     (∑h∈{0..<q}.
        (∑j∈{0..<4}.
          (∑r∈{0..<4 * Suc h}.
            of_int
              (N $$ (4 * Suc h-r-1,
                      4 * Suc h-j-1)) *
            brc_extend_x x xv1 $$
              (4 * Suc h-r-1,0))^2))"
  using prefix
  unfolding brc_minus_prefix_eliminated_def
  by simp

lemma brc_minus_prefix_eliminated_step:
  assumes prefix:
    "brc_minus_prefix_eliminated a b c d x xv1 q"
  assumes q_bound:
    "4 * q ≤ 𝗏"
  assumes before:
    "∀i. i < 4*q ⟶ i < 𝗏 ⟶
       x' $$ (i,0) = x $$ (i,0)"
  assumes local:
    "y_block_sqsum a b c d
       (brc_extend_x x' xv1) q
     =
     (∑j∈{0..<4}.
       (∑r∈{0..<4 * Suc q}.
         of_int
           (N $$ (4 * Suc q-r-1,
                   4 * Suc q-j-1)) *
         brc_extend_x x' xv1 $$
           (4 * Suc q-r-1,0))^2)"
  shows
    "brc_minus_prefix_eliminated
       a b c d x' xv1 (Suc q)"
proof -
  show ?thesis
    unfolding brc_minus_prefix_eliminated_def
  proof (intro allI impI)
    fix t
    assume t_lt: "t < Suc q"

    show
      "y_block_sqsum a b c d
         (brc_extend_x x' xv1) t
       =
       (∑j∈{0..<4}.
         (∑r∈{0..<4 * Suc t}.
           of_int
             (N $$ (4 * Suc t-r-1,
                     4 * Suc t-j-1)) *
           brc_extend_x x' xv1 $$
             (4 * Suc t-r-1,0))^2)"
    proof (cases "t < q")
      case True

      have block_bound:
        "4 * Suc t ≤ 4 * q"
        using True
        by simp

      have agree:
        "⋀i. i < 4 * Suc t ⟹
          brc_extend_x x' xv1 $$ (i,0) =
          brc_extend_x x xv1 $$ (i,0)"
      proof -
        fix i
        assume i_lt: "i < 4 * Suc t"

        have i_lt_4q:
          "i < 4*q"
          using i_lt block_bound
          by simp

        have i_lt_v:
          "i < 𝗏"
          using i_lt_4q q_bound
          by simp

        have xx:
          "x' $$ (i,0) = x $$ (i,0)"
          using before i_lt_4q i_lt_v
          by blast

        show
          "brc_extend_x x' xv1 $$ (i,0) =
           brc_extend_x x xv1 $$ (i,0)"
          using xx i_lt_v
          unfolding brc_extend_x_def
          by simp
      qed

      have old_block:
        "y_block_sqsum a b c d
           (brc_extend_x x' xv1) t
         =
         y_block_sqsum a b c d
           (brc_extend_x x xv1) t"
        unfolding y_block_sqsum_def
        using agree
        by simp

      have old_rhs:
        "(∑j∈{0..<4}.
          (∑r∈{0..<4 * Suc t}.
            of_int
              (N $$ (4 * Suc t-r-1,
                      4 * Suc t-j-1)) *
            brc_extend_x x' xv1 $$
              (4 * Suc t-r-1,0))^2)
         =
         (∑j∈{0..<4}.
          (∑r∈{0..<4 * Suc t}.
            of_int
              (N $$ (4 * Suc t-r-1,
                      4 * Suc t-j-1)) *
            brc_extend_x x xv1 $$
              (4 * Suc t-r-1,0))^2)"
      proof -
        have index_bound:
          "⋀r. r ∈ {0..<4 * Suc t} ⟹
             4 * Suc t-r-1 < 4 * Suc t"
          by simp

        show ?thesis
          using agree index_bound
          by (intro sum.cong) auto
      qed

      have old:
        "y_block_sqsum a b c d
           (brc_extend_x x xv1) t
         =
         (∑j∈{0..<4}.
           (∑r∈{0..<4 * Suc t}.
             of_int
               (N $$ (4 * Suc t-r-1,
                       4 * Suc t-j-1)) *
             brc_extend_x x xv1 $$
               (4 * Suc t-r-1,0))^2)"
        using prefix True
        unfolding brc_minus_prefix_eliminated_def
        by blast

      show ?thesis
        using old_block old_rhs old
        by simp
    next
      case False

      have tq:
        "t = q"
        using t_lt False
        by simp

      show ?thesis
        using local
        unfolding tq
        by simp
    qed
  qed
qed

definition brc_minus_local_step ::
  "nat ⇒ nat ⇒ nat ⇒ nat ⇒ rat ⇒ nat ⇒ bool" where
  "brc_minus_local_step a b c d xv1 q ⟷
     (∀x :: rat mat.
       4 * q ≤ 𝗏 ⟶
       (∃x' :: rat mat.
          (∀i. i < 4*q ⟶ i < 𝗏 ⟶
               x' $$ (i,0) = x $$ (i,0)) ∧
          y_block_sqsum a b c d
            (brc_extend_x x' xv1) q
          =
          (∑j∈{0..<4}.
            (∑r∈{0..<4 * Suc q}.
              of_int
                (N $$ (4 * Suc q-r-1,
                        4 * Suc q-j-1)) *
              brc_extend_x x' xv1 $$
                (4 * Suc q-r-1,0))^2)))"

lemma brc_minus_prefix_step_exists:
  assumes prefix:
    "brc_minus_prefix_eliminated a b c d x xv1 q"
  assumes q_bound:
    "4 * q ≤ 𝗏"
  assumes step:
    "brc_minus_local_step a b c d xv1 q"
  shows
    "∃x'.
       brc_minus_prefix_eliminated
         a b c d x' xv1 (Suc q)"
proof -
  obtain x' where before:
    "∀i. i < 4*q ⟶ i < 𝗏 ⟶
         x' $$ (i,0) = x $$ (i,0)"
    and local:
    "y_block_sqsum a b c d
       (brc_extend_x x' xv1) q
     =
     (∑j∈{0..<4}.
       (∑r∈{0..<4 * Suc q}.
         of_int
           (N $$ (4 * Suc q-r-1,
                   4 * Suc q-j-1)) *
         brc_extend_x x' xv1 $$
           (4 * Suc q-r-1,0))^2)"
    using step q_bound
    unfolding brc_minus_local_step_def
    by blast

  have
    "brc_minus_prefix_eliminated
       a b c d x' xv1 (Suc q)"
    using brc_minus_prefix_eliminated_step[
      OF prefix q_bound before local] .

  then show ?thesis
    by blast
qed

lemma brc_minus_prefix_exists_upto:
  assumes steps:
    "∀q<Q. brc_minus_local_step a b c d xv1 q"
  assumes bound:
    "4 * Q ≤ 𝗏"
  shows
    "∃x :: rat mat.
       brc_minus_prefix_eliminated
         a b c d x xv1 Q"
  using steps bound
proof (induction Q)
  case 0

  show ?case
    using brc_minus_prefix_eliminated_base
    by blast
next
  case (Suc Q)

  have steps_Q:
    "∀q<Q. brc_minus_local_step a b c d xv1 q"
    using Suc.prems(1)
    by simp

  have bound_Q:
    "4 * Q ≤ 𝗏"
    using Suc.prems(2)
    by simp

  obtain x :: "rat mat" where prefix:
    "brc_minus_prefix_eliminated
       a b c d x xv1 Q"
    using Suc.IH[OF steps_Q bound_Q]
    by blast

  have local_Q:
    "brc_minus_local_step a b c d xv1 Q"
    using Suc.prems(1)
    by simp

  obtain x' :: "rat mat" where next_prefix:
    "brc_minus_prefix_eliminated
       a b c d x' xv1 (Suc Q)"
    using brc_minus_prefix_step_exists[
      OF prefix bound_Q local_Q]
    by blast

  show ?case
    using next_prefix
    by blast
qed

lemma choose_y_linear_square:
  fixes A R :: rat
  shows "∃y :: rat. (A*y + R)^2 = y^2"
proof (cases "A = 1")
  case True

  have exists_y:
    "∃y :: rat. 2 * y = -R"
  proof
    show "2 * (-R / 2) = -R"
      by simp
  qed

  obtain y :: rat where hy:
    "2 * y = -R"
    using exists_y
    by blast

  have linear:
    "A * y + R = -y"
    using True hy
    by (simp add: algebra_simps)

  have square:
    "(A * y + R)^2 = y^2"
    using linear
    by simp

  show ?thesis
    using square
    by blast
next
  case False

  have denom:
    "1 - A ≠ 0"
    using False
    by simp

  have exists_y:
    "∃y :: rat. (1 - A) * y = R"
  proof
    show "(1 - A) * (R / (1 - A)) = R"
      using denom
      by simp
  qed

  obtain y :: rat where hy:
    "(1 - A) * y = R"
    using exists_y
    by blast

  have linear:
    "A * y + R = y"
    using hy
    by (simp add: algebra_simps)

  have square:
    "(A * y + R)^2 = y^2"
    using linear
    by simp

  show ?thesis
    using square
    by blast
qed

definition brc_linear_coeff ::
  "nat ⇒ nat ⇒ nat ⇒ nat ⇒ nat ⇒ nat ⇒ nat ⇒ rat" where
  "brc_linear_coeff a b c d m i j =
    (let D = of_nat (a^2 + b^2 + c^2 + d^2) :: rat in
     if j = 0 then
       of_int (N $$ (m-4,m-i-1)) * of_nat a / D +
       of_int (N $$ (m-3,m-i-1)) * of_nat b / D +
       of_int (N $$ (m-2,m-i-1)) * of_nat c / D +
       of_int (N $$ (m-1,m-i-1)) * of_nat d / D
     else if j = 1 then
       - of_int (N $$ (m-4,m-i-1)) * of_nat b / D +
         of_int (N $$ (m-3,m-i-1)) * of_nat a / D -
         of_int (N $$ (m-2,m-i-1)) * of_nat d / D +
         of_int (N $$ (m-1,m-i-1)) * of_nat c / D
     else if j = 2 then
       - of_int (N $$ (m-4,m-i-1)) * of_nat c / D +
         of_int (N $$ (m-3,m-i-1)) * of_nat d / D +
         of_int (N $$ (m-2,m-i-1)) * of_nat a / D -
         of_int (N $$ (m-1,m-i-1)) * of_nat b / D
     else
       - of_int (N $$ (m-4,m-i-1)) * of_nat d / D -
         of_int (N $$ (m-3,m-i-1)) * of_nat c / D +
         of_int (N $$ (m-2,m-i-1)) * of_nat b / D +
         of_int (N $$ (m-1,m-i-1)) * of_nat a / D)"

lemma brc_linear_coeff_0:
  "brc_linear_coeff a b c d m i 0 =
    (let D = of_nat (a^2 + b^2 + c^2 + d^2) :: rat in
       of_int (N $$ (m-4,m-i-1)) * of_nat a / D +
       of_int (N $$ (m-3,m-i-1)) * of_nat b / D +
       of_int (N $$ (m-2,m-i-1)) * of_nat c / D +
       of_int (N $$ (m-1,m-i-1)) * of_nat d / D)"
  unfolding brc_linear_coeff_def
  by simp

lemma brc_linear_coeff_1:
  "brc_linear_coeff a b c d m i 1 =
    (let D = of_nat (a^2 + b^2 + c^2 + d^2) :: rat in
       - of_int (N $$ (m-4,m-i-1)) * of_nat b / D +
         of_int (N $$ (m-3,m-i-1)) * of_nat a / D -
         of_int (N $$ (m-2,m-i-1)) * of_nat d / D +
         of_int (N $$ (m-1,m-i-1)) * of_nat c / D)"
  unfolding brc_linear_coeff_def
  by simp

lemma brc_linear_coeff_2:
  "brc_linear_coeff a b c d m i 2 =
    (let D = of_nat (a^2 + b^2 + c^2 + d^2) :: rat in
       - of_int (N $$ (m-4,m-i-1)) * of_nat c / D +
         of_int (N $$ (m-3,m-i-1)) * of_nat d / D +
         of_int (N $$ (m-2,m-i-1)) * of_nat a / D -
         of_int (N $$ (m-1,m-i-1)) * of_nat b / D)"
  unfolding brc_linear_coeff_def
  by simp

lemma brc_linear_coeff_3:
  "brc_linear_coeff a b c d m i 3 =
    (let D = of_nat (a^2 + b^2 + c^2 + d^2) :: rat in
       - of_int (N $$ (m-4,m-i-1)) * of_nat d / D -
         of_int (N $$ (m-3,m-i-1)) * of_nat c / D +
         of_int (N $$ (m-2,m-i-1)) * of_nat b / D +
         of_int (N $$ (m-1,m-i-1)) * of_nat a / D)"
  unfolding brc_linear_coeff_def
  by simp

definition brc_linear_tail ::
  "rat mat ⇒ nat ⇒ nat ⇒ rat" where
  "brc_linear_tail x m i =
    (∑h∈{4..<m}.
       of_int (N $$ (m-h-1,m-i-1)) *
       x $$ (m-h-1,0))"

lemma linear_comb_of_y_explicit:
  fixes a b c d :: nat
  fixes x :: "rat mat"
  fixes x0 x1 x2 x3 :: rat
  fixes i m :: nat
  assumes four_sq:
    "a^2 + b^2 + c^2 + d^2 = 𝗄 - Λ"
  assumes m_gt3:
    "3 < m"
  assumes i4:
    "i ∈ {0..<4}"
  assumes x0_def:
    "x0 = x $$ (m - 4, 0)"
  assumes x1_def:
    "x1 = x $$ (m - 3, 0)"
  assumes x2_def:
    "x2 = x $$ (m - 2, 0)"
  assumes x3_def:
    "x3 = x $$ (m - 1, 0)"
  shows
    "(∑h∈{0..<m}.
       of_int (N $$ (m - h - 1, m - i - 1)) *
       x $$ (m - h - 1, 0))
     =
       brc_linear_coeff a b c d m i 0 *
         one_of (y_of ((a,b,c,d),(x0,x1,x2,x3))) +
       brc_linear_coeff a b c d m i 1 *
         two_of (y_of ((a,b,c,d),(x0,x1,x2,x3))) +
       brc_linear_coeff a b c d m i 2 *
         three_of (y_of ((a,b,c,d),(x0,x1,x2,x3))) +
       brc_linear_coeff a b c d m i 3 *
         four_of (y_of ((a,b,c,d),(x0,x1,x2,x3))) +
       brc_linear_tail x m i"
proof -
  let ?D =
    "of_nat (a^2 + b^2 + c^2 + d^2) :: rat"

  let ?y0 =
    "one_of (y_of ((a,b,c,d),(x0,x1,x2,x3)))"

  let ?y1 =
    "two_of (y_of ((a,b,c,d),(x0,x1,x2,x3)))"

  let ?y2 =
    "three_of (y_of ((a,b,c,d),(x0,x1,x2,x3)))"

  let ?y3 =
    "four_of (y_of ((a,b,c,d),(x0,x1,x2,x3)))"

  have nz:
    "a^2 + b^2 + c^2 + d^2 ≠ 0"
  proof -
    have diff_pos:
      "0 < 𝗄 - Λ"
      using blocksize_gt_index
      by simp

    show ?thesis
      using four_sq diff_pos
      by simp
  qed

  have key:
    "y_inv_reversible
       (y_reversible ((a,b,c,d),(x0,x1,x2,x3)))
     =
     ((a,b,c,d),(x0,x1,x2,x3))"
    using y_inverses_part_1[OF nz, of x0 x1 x2 x3] .

  have x0_inv:
    "x0 =
       (of_nat a * ?y0 -
        of_nat b * ?y1 -
        of_nat c * ?y2 -
        of_nat d * ?y3) / ?D"
    using key
    by simp

  have x1_inv:
    "x1 =
       (of_nat b * ?y0 +
        of_nat a * ?y1 +
        of_nat d * ?y2 -
        of_nat c * ?y3) / ?D"
    using key
    by simp

  have x2_raw:
    "x2 =
       (of_nat c * ?y0 +
        of_nat a * ?y2 +
        of_nat b * ?y3 -
        of_nat d * ?y1) / ?D"
    using key
    by simp

  have x2_inv:
    "x2 =
       (of_nat c * ?y0 -
        of_nat d * ?y1 +
        of_nat a * ?y2 +
        of_nat b * ?y3) / ?D"
    using x2_raw
    by (simp add: algebra_simps)

  have x3_raw:
    "x3 =
       (of_nat d * ?y0 +
        of_nat c * ?y1 +
        of_nat a * ?y3 -
        of_nat b * ?y2) / ?D"
    using key
    by simp

  have x3_inv:
    "x3 =
       (of_nat d * ?y0 +
        of_nat c * ?y1 -
        of_nat b * ?y2 +
        of_nat a * ?y3) / ?D"
    using x3_raw
    by (simp add: algebra_simps)

  have interval_split:
    "{0..<m} = {0..<4} ∪ {4..<m}"
    using m_gt3
    by auto

  have interval_disjoint:
    "{0..<4} ∩ {4..<m} = {}"
    by auto

  have sum_split:
    "(∑h∈{0..<m}.
       of_int (N $$ (m - h - 1, m - i - 1)) *
       x $$ (m - h - 1, 0))
     =
     (∑h∈{0..<4}.
       of_int (N $$ (m - h - 1, m - i - 1)) *
       x $$ (m - h - 1, 0))
     +
     (∑h∈{4..<m}.
       of_int (N $$ (m - h - 1, m - i - 1)) *
       x $$ (m - h - 1, 0))"
    using interval_split interval_disjoint
    by (simp add: sum.union_disjoint)

  have first_four:
    "(∑h∈{0..<4}.
       of_int (N $$ (m - h - 1, m - i - 1)) *
       x $$ (m - h - 1, 0))
     =
       of_int (N $$ (m - 4, m - i - 1)) * x0 +
       of_int (N $$ (m - 3, m - i - 1)) * x1 +
       of_int (N $$ (m - 2, m - i - 1)) * x2 +
       of_int (N $$ (m - 1, m - i - 1)) * x3"
    using x0_def x1_def x2_def x3_def m_gt3
    by (simp add: numeral.simps(2,3) algebra_simps)

  have expanded:
    "(∑h∈{0..<4}.
       of_int (N $$ (m - h - 1, m - i - 1)) *
       x $$ (m - h - 1, 0))
     =
       brc_linear_coeff a b c d m i 0 * ?y0 +
       brc_linear_coeff a b c d m i 1 * ?y1 +
       brc_linear_coeff a b c d m i 2 * ?y2 +
       brc_linear_coeff a b c d m i 3 * ?y3"
  proof -
    have
      "(∑h∈{0..<4}.
         of_int (N $$ (m - h - 1, m - i - 1)) *
         x $$ (m - h - 1, 0))
       =
         of_int (N $$ (m - 4, m - i - 1)) * x0 +
         of_int (N $$ (m - 3, m - i - 1)) * x1 +
         of_int (N $$ (m - 2, m - i - 1)) * x2 +
         of_int (N $$ (m - 1, m - i - 1)) * x3"
      using first_four .

    also have
      "... =
       of_int (N $$ (m - 4, m - i - 1)) *
         ((of_nat a * ?y0 -
           of_nat b * ?y1 -
           of_nat c * ?y2 -
           of_nat d * ?y3) / ?D) +
       of_int (N $$ (m - 3, m - i - 1)) *
         ((of_nat b * ?y0 +
           of_nat a * ?y1 +
           of_nat d * ?y2 -
           of_nat c * ?y3) / ?D) +
       of_int (N $$ (m - 2, m - i - 1)) *
         ((of_nat c * ?y0 -
           of_nat d * ?y1 +
           of_nat a * ?y2 +
           of_nat b * ?y3) / ?D) +
       of_int (N $$ (m - 1, m - i - 1)) *
         ((of_nat d * ?y0 +
           of_nat c * ?y1 -
           of_nat b * ?y2 +
           of_nat a * ?y3) / ?D)"
      using x0_inv x1_inv x2_inv x3_inv
      by simp

    also have
      "... =
       brc_linear_coeff a b c d m i 0 * ?y0 +
       brc_linear_coeff a b c d m i 1 * ?y1 +
       brc_linear_coeff a b c d m i 2 * ?y2 +
       brc_linear_coeff a b c d m i 3 * ?y3"
    proof -
      let ?A0 = "of_int (N $$ (m-4, m-i-1)) :: rat"
      let ?A1 = "of_int (N $$ (m-3, m-i-1)) :: rat"
      let ?A2 = "of_int (N $$ (m-2, m-i-1)) :: rat"
      let ?A3 = "of_int (N $$ (m-1, m-i-1)) :: rat"

      have part0:
        "?A0 *
           ((of_nat a * ?y0 -
             of_nat b * ?y1 -
             of_nat c * ?y2 -
             of_nat d * ?y3) / ?D)
         =
           (?A0 * of_nat a / ?D) * ?y0 -
           (?A0 * of_nat b / ?D) * ?y1 -
           (?A0 * of_nat c / ?D) * ?y2 -
           (?A0 * of_nat d / ?D) * ?y3"
        by (simp only:
            divide_inverse
            diff_conv_add_uminus
            distrib_left
            distrib_right
            minus_mult_left
            minus_mult_right
            mult.assoc mult.commute mult.left_commute
            add.assoc add.commute add.left_commute)

      have part1:
        "?A1 *
           ((of_nat b * ?y0 +
             of_nat a * ?y1 +
             of_nat d * ?y2 -
             of_nat c * ?y3) / ?D)
         =
           (?A1 * of_nat b / ?D) * ?y0 +
           (?A1 * of_nat a / ?D) * ?y1 +
           (?A1 * of_nat d / ?D) * ?y2 -
           (?A1 * of_nat c / ?D) * ?y3"
        by (simp only:
            divide_inverse
            diff_conv_add_uminus
            distrib_left
            distrib_right
            minus_mult_left
            minus_mult_right
            mult.assoc mult.commute mult.left_commute
            add.assoc add.commute add.left_commute)

      have part2:
        "?A2 *
           ((of_nat c * ?y0 -
             of_nat d * ?y1 +
             of_nat a * ?y2 +
             of_nat b * ?y3) / ?D)
         =
           (?A2 * of_nat c / ?D) * ?y0 -
           (?A2 * of_nat d / ?D) * ?y1 +
           (?A2 * of_nat a / ?D) * ?y2 +
           (?A2 * of_nat b / ?D) * ?y3"
        by (simp only:
            divide_inverse
            diff_conv_add_uminus
            distrib_left
            distrib_right
            minus_mult_left
            minus_mult_right
            mult.assoc mult.commute mult.left_commute
            add.assoc add.commute add.left_commute)

      have part3:
        "?A3 *
           ((of_nat d * ?y0 +
             of_nat c * ?y1 -
             of_nat b * ?y2 +
             of_nat a * ?y3) / ?D)
         =
           (?A3 * of_nat d / ?D) * ?y0 +
           (?A3 * of_nat c / ?D) * ?y1 -
           (?A3 * of_nat b / ?D) * ?y2 +
           (?A3 * of_nat a / ?D) * ?y3"
        by (simp only:
            divide_inverse
            diff_conv_add_uminus
            distrib_left
            distrib_right
            minus_mult_left
            minus_mult_right
            mult.assoc mult.commute mult.left_commute
            add.assoc add.commute add.left_commute)

      have group0:
        "(?A0 * of_nat a / ?D +
          ?A1 * of_nat b / ?D +
          ?A2 * of_nat c / ?D +
          ?A3 * of_nat d / ?D) * ?y0
         =
          (?A0 * of_nat a / ?D) * ?y0 +
          (?A1 * of_nat b / ?D) * ?y0 +
          (?A2 * of_nat c / ?D) * ?y0 +
          (?A3 * of_nat d / ?D) * ?y0"
        by (simp only:
            divide_inverse
            diff_conv_add_uminus
            distrib_left distrib_right
            minus_mult_left minus_mult_right
            mult.assoc mult.commute mult.left_commute
            add.assoc add.commute add.left_commute)

      have group1:
        "(- ?A0 * of_nat b / ?D +
            ?A1 * of_nat a / ?D -
            ?A2 * of_nat d / ?D +
            ?A3 * of_nat c / ?D) * ?y1
         =
          - (?A0 * of_nat b / ?D) * ?y1 +
            (?A1 * of_nat a / ?D) * ?y1 -
            (?A2 * of_nat d / ?D) * ?y1 +
            (?A3 * of_nat c / ?D) * ?y1"
        by (simp only:
            divide_inverse
            diff_conv_add_uminus
            distrib_left distrib_right
            minus_mult_left minus_mult_right
            mult.assoc mult.commute mult.left_commute
            add.assoc add.commute add.left_commute)

      have group2:
        "(- ?A0 * of_nat c / ?D +
            ?A1 * of_nat d / ?D +
            ?A2 * of_nat a / ?D -
            ?A3 * of_nat b / ?D) * ?y2
         =
          - (?A0 * of_nat c / ?D) * ?y2 +
            (?A1 * of_nat d / ?D) * ?y2 +
            (?A2 * of_nat a / ?D) * ?y2 -
            (?A3 * of_nat b / ?D) * ?y2"
        by (simp only:
            divide_inverse
            diff_conv_add_uminus
            distrib_left distrib_right
            minus_mult_left minus_mult_right
            mult.assoc mult.commute mult.left_commute
            add.assoc add.commute add.left_commute)

      have group3:
        "(- ?A0 * of_nat d / ?D -
            ?A1 * of_nat c / ?D +
            ?A2 * of_nat b / ?D +
            ?A3 * of_nat a / ?D) * ?y3
         =
          - (?A0 * of_nat d / ?D) * ?y3 -
            (?A1 * of_nat c / ?D) * ?y3 +
            (?A2 * of_nat b / ?D) * ?y3 +
            (?A3 * of_nat a / ?D) * ?y3"
        by (simp only:
            divide_inverse
            diff_conv_add_uminus
            distrib_left distrib_right
            minus_mult_left minus_mult_right
            mult.assoc mult.commute mult.left_commute
            add.assoc add.commute add.left_commute)

      have combined:
        "?A0 *
           ((of_nat a * ?y0 -
             of_nat b * ?y1 -
             of_nat c * ?y2 -
             of_nat d * ?y3) / ?D) +
         ?A1 *
           ((of_nat b * ?y0 +
             of_nat a * ?y1 +
             of_nat d * ?y2 -
             of_nat c * ?y3) / ?D) +
         ?A2 *
           ((of_nat c * ?y0 -
             of_nat d * ?y1 +
             of_nat a * ?y2 +
             of_nat b * ?y3) / ?D) +
         ?A3 *
           ((of_nat d * ?y0 +
             of_nat c * ?y1 -
             of_nat b * ?y2 +
             of_nat a * ?y3) / ?D)
         =
         (?A0 * of_nat a / ?D +
          ?A1 * of_nat b / ?D +
          ?A2 * of_nat c / ?D +
          ?A3 * of_nat d / ?D) * ?y0 +
         (- ?A0 * of_nat b / ?D +
            ?A1 * of_nat a / ?D -
            ?A2 * of_nat d / ?D +
            ?A3 * of_nat c / ?D) * ?y1 +
         (- ?A0 * of_nat c / ?D +
            ?A1 * of_nat d / ?D +
            ?A2 * of_nat a / ?D -
            ?A3 * of_nat b / ?D) * ?y2 +
         (- ?A0 * of_nat d / ?D -
            ?A1 * of_nat c / ?D +
            ?A2 * of_nat b / ?D +
            ?A3 * of_nat a / ?D) * ?y3"
        apply (subst part0)
        apply (subst part1)
        apply (subst part2)
        apply (subst part3)
        apply (subst group0)
        apply (subst group1)
        apply (subst group2)
        apply (subst group3)
        by (simp only:
            diff_conv_add_uminus
            minus_mult_left
            minus_mult_right
            add.assoc add.commute add.left_commute)

      show ?thesis
        using combined
        by (simp only:
            brc_linear_coeff_0
            brc_linear_coeff_1
            brc_linear_coeff_2
            brc_linear_coeff_3
            Let_def)
    qed

    finally show ?thesis .
  qed

  show ?thesis
    using sum_split expanded
    unfolding brc_linear_tail_def
    by simp
qed

lemma brc_minus_block_linear_explicit:
  fixes a b c d q i :: nat
  fixes x :: "rat mat"
  assumes four_sq:
    "a^2 + b^2 + c^2 + d^2 = 𝗄 - Λ"
  assumes block_bound:
    "4 * Suc q ≤ 𝗏"
  assumes i4:
    "i < 4"
  shows
    "(∑r∈{0..<4 * Suc q}.
       of_int
         (N $$ (4 * Suc q-r-1,
                 4 * Suc q-i-1)) *
       x $$ (4 * Suc q-r-1,0))
     =
       brc_linear_coeff
         a b c d (4 * Suc q) i 0 *
       one_of
         (y_of
           ((a,b,c,d),
            (x $$ (4*q,0),
             x $$ (4*q+1,0),
             x $$ (4*q+2,0),
             x $$ (4*q+3,0)))) +
       brc_linear_coeff
         a b c d (4 * Suc q) i 1 *
       two_of
         (y_of
           ((a,b,c,d),
            (x $$ (4*q,0),
             x $$ (4*q+1,0),
             x $$ (4*q+2,0),
             x $$ (4*q+3,0)))) +
       brc_linear_coeff
         a b c d (4 * Suc q) i 2 *
       three_of
         (y_of
           ((a,b,c,d),
            (x $$ (4*q,0),
             x $$ (4*q+1,0),
             x $$ (4*q+2,0),
             x $$ (4*q+3,0)))) +
       brc_linear_coeff
         a b c d (4 * Suc q) i 3 *
       four_of
         (y_of
           ((a,b,c,d),
            (x $$ (4*q,0),
             x $$ (4*q+1,0),
             x $$ (4*q+2,0),
             x $$ (4*q+3,0)))) +
       brc_linear_tail x (4 * Suc q) i"
proof -
  let ?m = "4 * Suc q"

  have m_gt3:
    "3 < ?m"
    by simp

  have i_mem:
    "i ∈ {0..<4}"
    using i4
    by simp

  have x0:
    "x $$ (4*q,0) = x $$ (?m-4,0)"
    by simp

  have x1:
    "x $$ (4*q+1,0) = x $$ (?m-3,0)"
    by simp

  have x2:
    "x $$ (4*q+2,0) = x $$ (?m-2,0)"
    by simp

  have x3:
    "x $$ (4*q+3,0) = x $$ (?m-1,0)"
    by (simp add: add.commute)

  show ?thesis
    using linear_comb_of_y_explicit[
      OF four_sq m_gt3 i_mem
         x0 x1 x2 x3]
    by simp
qed

lemma brc_minus_extended_block_linear_explicit:
  fixes a b c d q i :: nat
  fixes x :: "rat mat"
  fixes xv1 :: rat
  assumes four_sq:
    "a^2 + b^2 + c^2 + d^2 = 𝗄 - Λ"
  assumes block_bound:
    "4 * Suc q ≤ 𝗏"
  assumes i4:
    "i < 4"
  shows
    "(∑r∈{0..<4 * Suc q}.
       of_int
         (N $$ (4 * Suc q-r-1,
                 4 * Suc q-i-1)) *
       brc_extend_x x xv1 $$ (4 * Suc q-r-1,0))
     =
       brc_linear_coeff a b c d (4 * Suc q) i 0 *
         one_of
           (y_of
             ((a,b,c,d),
              (brc_extend_x x xv1 $$ (4*q,0),
               brc_extend_x x xv1 $$ (4*q+1,0),
               brc_extend_x x xv1 $$ (4*q+2,0),
               brc_extend_x x xv1 $$ (4*q+3,0)))) +
       brc_linear_coeff a b c d (4 * Suc q) i 1 *
         two_of
           (y_of
             ((a,b,c,d),
              (brc_extend_x x xv1 $$ (4*q,0),
               brc_extend_x x xv1 $$ (4*q+1,0),
               brc_extend_x x xv1 $$ (4*q+2,0),
               brc_extend_x x xv1 $$ (4*q+3,0)))) +
       brc_linear_coeff a b c d (4 * Suc q) i 2 *
         three_of
           (y_of
             ((a,b,c,d),
              (brc_extend_x x xv1 $$ (4*q,0),
               brc_extend_x x xv1 $$ (4*q+1,0),
               brc_extend_x x xv1 $$ (4*q+2,0),
               brc_extend_x x xv1 $$ (4*q+3,0)))) +
       brc_linear_coeff a b c d (4 * Suc q) i 3 *
         four_of
           (y_of
             ((a,b,c,d),
              (brc_extend_x x xv1 $$ (4*q,0),
               brc_extend_x x xv1 $$ (4*q+1,0),
               brc_extend_x x xv1 $$ (4*q+2,0),
               brc_extend_x x xv1 $$ (4*q+3,0)))) +
       brc_linear_tail
         (brc_extend_x x xv1) (4 * Suc q) i"
  using brc_minus_block_linear_explicit[
    OF four_sq block_bound i4,
    of "brc_extend_x x xv1"]
  .

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

lemma brc_match_y_affine:
  "brc_match_y A (B * y + R) =
   brc_match_coeff A B * y + brc_match_y A R"
proof (cases "A = 1")
  case True

  have A1:
    "A = 1"
    using True .

  show ?thesis
    unfolding brc_match_y_def brc_match_coeff_def
    using A1
    by (simp; argo)
next
  case False

  have A1:
    "A ≠ 1"
    using False .

  show ?thesis
    unfolding brc_match_y_def brc_match_coeff_def
    using A1
    by (simp add:
        add_divide_distrib
        algebra_simps)
qed

lemma brc_two_linear_squares:
  fixes a b c d r s :: rat
  shows
    "∃x y :: rat.
       (a*x + b*y + r)^2 +
       (c*x + d*y + s)^2
       =
       x^2 + y^2"
proof -
  let ?p = "brc_match_coeff a b"
  let ?q = "brc_match_y a r"

  let ?A = "c * ?p + d"
  let ?R = "c * ?q + s"

  let ?y = "brc_match_y ?A ?R"
  let ?x = "brc_match_y a (b * ?y + r)"

  have cancel_x:
    "(a * ?x + (b * ?y + r))^2 = ?x^2"
    using brc_match_y_square[
      of a "b * ?y + r"]
    by simp

  have first_square:
    "(a * ?x + b * ?y + r)^2 = ?x^2"
    using cancel_x
    by (simp only: add.assoc)

  have x_affine:
    "?x = ?p * ?y + ?q"
    using brc_match_y_affine[
      of a b ?y r]
    by simp

  have second_form:
    "c * ?x + d * ?y + s =
     ?A * ?y + ?R"
    using x_affine
    by (simp add: algebra_simps)

  have cancel_y:
    "(?A * ?y + ?R)^2 = ?y^2"
    using brc_match_y_square[
      of ?A ?R]
    by simp

  have second_square:
    "(c * ?x + d * ?y + s)^2 = ?y^2"
    using second_form cancel_y
    by metis

  have
    "(a * ?x + b * ?y + r)^2 +
     (c * ?x + d * ?y + s)^2
     =
     ?x^2 + ?y^2"
    using first_square second_square
    by simp

  then show ?thesis
    by blast
qed

lemma brc_match_y_affine2:
  "brc_match_y A (B * y + C * z + R) =
   brc_match_coeff A B * y +
   brc_match_coeff A C * z +
   brc_match_y A R"
proof -
  have regroup:
    "B * y + C * z + R =
     B * y + (C * z + R)"
    by (simp add: add.assoc)

  have step1:
    "brc_match_y A (B * y + (C * z + R)) =
     brc_match_coeff A B * y +
     brc_match_y A (C * z + R)"
    using brc_match_y_affine[
      of A B y "C * z + R"] .

  have step2:
    "brc_match_y A (C * z + R) =
     brc_match_coeff A C * z +
     brc_match_y A R"
    using brc_match_y_affine[
      of A C z R] .

  show ?thesis
    using regroup step1 step2
    by (simp add: add.assoc)
qed

lemma brc_three_linear_squares:
  fixes a0 b0 c0 r0 :: rat
  fixes a1 b1 c1 r1 :: rat
  fixes a2 b2 c2 r2 :: rat
  shows
    "∃x y z :: rat.
       (a0*x + b0*y + c0*z + r0)^2 +
       (a1*x + b1*y + c1*z + r1)^2 +
       (a2*x + b2*y + c2*z + r2)^2
       =
       x^2 + y^2 + z^2"
proof -
  let ?p = "brc_match_coeff a0 b0"
  let ?q = "brc_match_coeff a0 c0"
  let ?t = "brc_match_y a0 r0"

  let ?a1 = "a1 * ?p + b1"
  let ?b1 = "a1 * ?q + c1"
  let ?r1 = "a1 * ?t + r1"

  let ?a2 = "a2 * ?p + b2"
  let ?b2 = "a2 * ?q + c2"
  let ?r2 = "a2 * ?t + r2"

  obtain y z :: rat where yz:
    "(?a1*y + ?b1*z + ?r1)^2 +
     (?a2*y + ?b2*z + ?r2)^2
     =
     y^2 + z^2"
    using brc_two_linear_squares[
      where a="?a1"
        and b="?b1"
        and c="?a2"
        and d="?b2"
        and r="?r1"
        and s="?r2"]
    by blast

  let ?x =
    "brc_match_y a0 (b0*y + c0*z + r0)"

  have cancel_x:
    "(a0 * ?x + (b0*y + c0*z + r0))^2 =
     ?x^2"
    using brc_match_y_square[
      of a0 "b0*y + c0*z + r0"]
    by simp

  have first_square:
    "(a0*?x + b0*y + c0*z + r0)^2 =
     ?x^2"
    using cancel_x
    by (simp only: add.assoc)

  have x_affine:
    "?x = ?p*y + ?q*z + ?t"
    using brc_match_y_affine2[
      of a0 b0 y c0 z r0]
    by simp

  have second_form:
    "a1*?x + b1*y + c1*z + r1 =
     ?a1*y + ?b1*z + ?r1"
    using x_affine
    by (simp add: algebra_simps)

  have third_form:
    "a2*?x + b2*y + c2*z + r2 =
     ?a2*y + ?b2*z + ?r2"
    using x_affine
    by (simp add: algebra_simps)

  have remaining:
    "(a1*?x + b1*y + c1*z + r1)^2 +
     (a2*?x + b2*y + c2*z + r2)^2
     =
     y^2 + z^2"
    using second_form third_form yz
    by metis

  have total:
    "(a0*?x + b0*y + c0*z + r0)^2 +
     (a1*?x + b1*y + c1*z + r1)^2 +
     (a2*?x + b2*y + c2*z + r2)^2
     =
     ?x^2 + y^2 + z^2"
  proof -
    have
      "(a0*?x + b0*y + c0*z + r0)^2 +
       (a1*?x + b1*y + c1*z + r1)^2 +
       (a2*?x + b2*y + c2*z + r2)^2
       =
       (a0*?x + b0*y + c0*z + r0)^2 +
       ((a1*?x + b1*y + c1*z + r1)^2 +
        (a2*?x + b2*y + c2*z + r2)^2)"
      by (simp only: add.assoc)

    also have
      "... = ?x^2 + (y^2 + z^2)"
      using first_square remaining
      by simp

    also have
      "... = ?x^2 + y^2 + z^2"
      by (simp only: add.assoc)

    finally show ?thesis .
  qed

  show ?thesis
    using total
    by blast
qed

lemma brc_match_y_affine3:
  "brc_match_y A (B*x + C*y + D*z + R) =
   brc_match_coeff A B * x +
   brc_match_coeff A C * y +
   brc_match_coeff A D * z +
   brc_match_y A R"
proof -
  have regroup:
    "B*x + C*y + D*z + R =
     B*x + (C*y + D*z + R)"
    by (simp add: add.assoc)

  have step1:
    "brc_match_y A (B*x + (C*y + D*z + R)) =
     brc_match_coeff A B * x +
     brc_match_y A (C*y + D*z + R)"
    using brc_match_y_affine[
      of A B x "C*y + D*z + R"] .

  have step2:
    "brc_match_y A (C*y + D*z + R) =
     brc_match_coeff A C * y +
     brc_match_coeff A D * z +
     brc_match_y A R"
    using brc_match_y_affine2[
      of A C y D z R] .

  show ?thesis
    using regroup step1 step2
    by (simp add: add.assoc)
qed

lemma brc_four_linear_squares:
  fixes a0 b0 c0 d0 r0 :: rat
  fixes a1 b1 c1 d1 r1 :: rat
  fixes a2 b2 c2 d2 r2 :: rat
  fixes a3 b3 c3 d3 r3 :: rat
  shows
    "∃x y z w :: rat.
       (a0*x + b0*y + c0*z + d0*w + r0)^2 +
       (a1*x + b1*y + c1*z + d1*w + r1)^2 +
       (a2*x + b2*y + c2*z + d2*w + r2)^2 +
       (a3*x + b3*y + c3*z + d3*w + r3)^2
       =
       x^2 + y^2 + z^2 + w^2"
proof -
  let ?p = "brc_match_coeff a0 b0"
  let ?q = "brc_match_coeff a0 c0"
  let ?u = "brc_match_coeff a0 d0"
  let ?t = "brc_match_y a0 r0"

  let ?a1 = "a1 * ?p + b1"
  let ?b1 = "a1 * ?q + c1"
  let ?c1 = "a1 * ?u + d1"
  let ?r1 = "a1 * ?t + r1"

  let ?a2 = "a2 * ?p + b2"
  let ?b2 = "a2 * ?q + c2"
  let ?c2 = "a2 * ?u + d2"
  let ?r2 = "a2 * ?t + r2"

  let ?a3 = "a3 * ?p + b3"
  let ?b3 = "a3 * ?q + c3"
  let ?c3 = "a3 * ?u + d3"
  let ?r3 = "a3 * ?t + r3"

  obtain y z w :: rat where yzw:
    "(?a1*y + ?b1*z + ?c1*w + ?r1)^2 +
     (?a2*y + ?b2*z + ?c2*w + ?r2)^2 +
     (?a3*y + ?b3*z + ?c3*w + ?r3)^2
     =
     y^2 + z^2 + w^2"
    using brc_three_linear_squares
    by blast

  let ?x =
    "brc_match_y a0 (b0*y + c0*z + d0*w + r0)"

  have cancel_x:
    "(a0 * ?x + (b0*y + c0*z + d0*w + r0))^2 =
     ?x^2"
    using brc_match_y_square[
      of a0 "b0*y + c0*z + d0*w + r0"]
    by simp

  have first_square:
    "(a0*?x + b0*y + c0*z + d0*w + r0)^2 =
     ?x^2"
    using cancel_x
    by (simp only: add.assoc)

  have x_affine:
    "?x = ?p*y + ?q*z + ?u*w + ?t"
    using brc_match_y_affine3[
      of a0 b0 y c0 z d0 w r0]
    by simp

  have second_form:
    "a1*?x + b1*y + c1*z + d1*w + r1 =
     ?a1*y + ?b1*z + ?c1*w + ?r1"
    using x_affine
    by (simp add: algebra_simps)

  have third_form:
    "a2*?x + b2*y + c2*z + d2*w + r2 =
     ?a2*y + ?b2*z + ?c2*w + ?r2"
    using x_affine
    by (simp add: algebra_simps)

  have fourth_form:
    "a3*?x + b3*y + c3*z + d3*w + r3 =
     ?a3*y + ?b3*z + ?c3*w + ?r3"
    using x_affine
    by (simp add: algebra_simps)

  have remaining:
    "(a1*?x + b1*y + c1*z + d1*w + r1)^2 +
     (a2*?x + b2*y + c2*z + d2*w + r2)^2 +
     (a3*?x + b3*y + c3*z + d3*w + r3)^2
     =
     y^2 + z^2 + w^2"
    using second_form third_form fourth_form yzw
    by metis

  have total:
    "(a0*?x + b0*y + c0*z + d0*w + r0)^2 +
     (a1*?x + b1*y + c1*z + d1*w + r1)^2 +
     (a2*?x + b2*y + c2*z + d2*w + r2)^2 +
     (a3*?x + b3*y + c3*z + d3*w + r3)^2
     =
     ?x^2 + y^2 + z^2 + w^2"
  proof -
    have
      "(a0*?x + b0*y + c0*z + d0*w + r0)^2 +
       (a1*?x + b1*y + c1*z + d1*w + r1)^2 +
       (a2*?x + b2*y + c2*z + d2*w + r2)^2 +
       (a3*?x + b3*y + c3*z + d3*w + r3)^2
       =
       (a0*?x + b0*y + c0*z + d0*w + r0)^2 +
       ((a1*?x + b1*y + c1*z + d1*w + r1)^2 +
        (a2*?x + b2*y + c2*z + d2*w + r2)^2 +
        (a3*?x + b3*y + c3*z + d3*w + r3)^2)"
      by (simp only: add.assoc)

    also have
      "... = ?x^2 + (y^2 + z^2 + w^2)"
      using first_square remaining
      by simp

    also have
      "... = ?x^2 + y^2 + z^2 + w^2"
      by (simp only: add.assoc)

    finally show ?thesis .
  qed

  show ?thesis
    using total
    by blast
qed

lemma brc_four_linear_squares_coeff:
  fixes C :: "nat ⇒ nat ⇒ rat"
  fixes R :: "nat ⇒ rat"
  shows
    "∃y0 y1 y2 y3 :: rat.
       (C 0 0*y0 + C 0 1*y1 +
        C 0 2*y2 + C 0 3*y3 + R 0)^2 +
       (C 1 0*y0 + C 1 1*y1 +
        C 1 2*y2 + C 1 3*y3 + R 1)^2 +
       (C 2 0*y0 + C 2 1*y1 +
        C 2 2*y2 + C 2 3*y3 + R 2)^2 +
       (C 3 0*y0 + C 3 1*y1 +
        C 3 2*y2 + C 3 3*y3 + R 3)^2
       =
       y0^2 + y1^2 + y2^2 + y3^2"
  using brc_four_linear_squares[
    of "C 0 0" "C 0 1" "C 0 2" "C 0 3" "R 0"
       "C 1 0" "C 1 1" "C 1 2" "C 1 3" "R 1"
       "C 2 0" "C 2 1" "C 2 2" "C 2 3" "R 2"
       "C 3 0" "C 3 1" "C 3 2" "C 3 3" "R 3"]
  .

lemma brc_minus_choose_block_y:
  fixes a b c d q :: nat
  fixes x :: "rat mat"
  fixes xv1 :: rat
  shows
    "∃y0 y1 y2 y3 :: rat.
       (brc_linear_coeff a b c d (4 * Suc q) 0 0 * y0 +
        brc_linear_coeff a b c d (4 * Suc q) 0 1 * y1 +
        brc_linear_coeff a b c d (4 * Suc q) 0 2 * y2 +
        brc_linear_coeff a b c d (4 * Suc q) 0 3 * y3 +
        brc_linear_tail
          (brc_extend_x x xv1) (4 * Suc q) 0)^2 +
       (brc_linear_coeff a b c d (4 * Suc q) 1 0 * y0 +
        brc_linear_coeff a b c d (4 * Suc q) 1 1 * y1 +
        brc_linear_coeff a b c d (4 * Suc q) 1 2 * y2 +
        brc_linear_coeff a b c d (4 * Suc q) 1 3 * y3 +
        brc_linear_tail
          (brc_extend_x x xv1) (4 * Suc q) 1)^2 +
       (brc_linear_coeff a b c d (4 * Suc q) 2 0 * y0 +
        brc_linear_coeff a b c d (4 * Suc q) 2 1 * y1 +
        brc_linear_coeff a b c d (4 * Suc q) 2 2 * y2 +
        brc_linear_coeff a b c d (4 * Suc q) 2 3 * y3 +
        brc_linear_tail
          (brc_extend_x x xv1) (4 * Suc q) 2)^2 +
       (brc_linear_coeff a b c d (4 * Suc q) 3 0 * y0 +
        brc_linear_coeff a b c d (4 * Suc q) 3 1 * y1 +
        brc_linear_coeff a b c d (4 * Suc q) 3 2 * y2 +
        brc_linear_coeff a b c d (4 * Suc q) 3 3 * y3 +
        brc_linear_tail
          (brc_extend_x x xv1) (4 * Suc q) 3)^2
       =
       y0^2 + y1^2 + y2^2 + y3^2"
  using brc_four_linear_squares_coeff[
    where C =
      "λi j. brc_linear_coeff
         a b c d (4 * Suc q) i j"
      and R =
      "λi. brc_linear_tail
         (brc_extend_x x xv1) (4 * Suc q) i"]
  by simp

definition brc_minus_affine_match ::
  "nat ⇒ nat ⇒ nat ⇒ nat ⇒ rat mat ⇒ rat ⇒ nat ⇒
   rat ⇒ rat ⇒ rat ⇒ rat ⇒ bool" where
  "brc_minus_affine_match a b c d x xv1 q y0 y1 y2 y3 ⟷
     (brc_linear_coeff a b c d (4 * Suc q) 0 0 * y0 +
      brc_linear_coeff a b c d (4 * Suc q) 0 1 * y1 +
      brc_linear_coeff a b c d (4 * Suc q) 0 2 * y2 +
      brc_linear_coeff a b c d (4 * Suc q) 0 3 * y3 +
      brc_linear_tail
        (brc_extend_x x xv1) (4 * Suc q) 0)^2 +
     (brc_linear_coeff a b c d (4 * Suc q) 1 0 * y0 +
      brc_linear_coeff a b c d (4 * Suc q) 1 1 * y1 +
      brc_linear_coeff a b c d (4 * Suc q) 1 2 * y2 +
      brc_linear_coeff a b c d (4 * Suc q) 1 3 * y3 +
      brc_linear_tail
        (brc_extend_x x xv1) (4 * Suc q) 1)^2 +
     (brc_linear_coeff a b c d (4 * Suc q) 2 0 * y0 +
      brc_linear_coeff a b c d (4 * Suc q) 2 1 * y1 +
      brc_linear_coeff a b c d (4 * Suc q) 2 2 * y2 +
      brc_linear_coeff a b c d (4 * Suc q) 2 3 * y3 +
      brc_linear_tail
        (brc_extend_x x xv1) (4 * Suc q) 2)^2 +
     (brc_linear_coeff a b c d (4 * Suc q) 3 0 * y0 +
      brc_linear_coeff a b c d (4 * Suc q) 3 1 * y1 +
      brc_linear_coeff a b c d (4 * Suc q) 3 2 * y2 +
      brc_linear_coeff a b c d (4 * Suc q) 3 3 * y3 +
      brc_linear_tail
        (brc_extend_x x xv1) (4 * Suc q) 3)^2
     =
     y0^2 + y1^2 + y2^2 + y3^2"

lemma brc_minus_affine_match_exists:
  "∃y0 y1 y2 y3 :: rat.
     brc_minus_affine_match
       a b c d x xv1 q y0 y1 y2 y3"
  using brc_minus_choose_block_y[
    of a b c d q x xv1]
  unfolding brc_minus_affine_match_def
  by blast

lemma brc_minus_affine_match_update_exists:
  fixes a b c d q :: nat
  fixes x :: "rat mat"
  fixes xv1 :: rat
  assumes nzsum:
    "a^2 + b^2 + c^2 + d^2 ≠ 0"
  assumes block_bound:
    "4 * Suc q ≤ 𝗏"
  shows
    "∃x' y0 y1 y2 y3.
       brc_minus_affine_match
         a b c d x xv1 q y0 y1 y2 y3 ∧
       (∀i. i < 4*q ⟶ i < 𝗏 ⟶
          x' $$ (i,0) = x $$ (i,0)) ∧
       y_block_sqsum a b c d x' q =
         y0^2 + y1^2 + y2^2 + y3^2"
proof -
  obtain y0 y1 y2 y3 :: rat where match:
    "brc_minus_affine_match
       a b c d x xv1 q y0 y1 y2 y3"
    using brc_minus_affine_match_exists[
      of a b c d x xv1 q]
    by blast

  have b0:
    "4*q < 𝗏"
    using block_bound
    by simp

  have b1:
    "4*q + 1 < 𝗏"
    using block_bound
    by simp

  have b2:
    "4*q + 2 < 𝗏"
    using block_bound
    by simp

  have b3:
    "4*q + 3 < 𝗏"
    using block_bound
    by simp

  let ?x0 =
    "one_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"

  let ?x1 =
    "two_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"

  let ?x2 =
    "three_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"

  let ?x3 =
    "four_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"

  let ?x' =
    "update_x_block x q ?x0 ?x1 ?x2 ?x3"

  have preserve:
    "∀i. i < 4*q ⟶ i < 𝗏 ⟶
       ?x' $$ (i,0) = x $$ (i,0)"
  proof (intro allI impI)
    fix i
    assume conditions:
      "i < 4*q"
      "i < 𝗏"

    show "?x' $$ (i,0) = x $$ (i,0)"
      using update_x_block_preserve_before[
        OF conditions, of x ?x0 ?x1 ?x2 ?x3]
      .
  qed

  have block_sum:
    "y_block_sqsum a b c d ?x' q =
     y0^2 + y1^2 + y2^2 + y3^2"
    using y_block_sqsum_update_y_inv[
      OF nzsum b0 b1 b2 b3,
      of x y0 y1 y2 y3]
    by simp

  show ?thesis
    using match preserve block_sum
    by blast
qed

lemma brc_extend_x_y_block_below:
  fixes a b c d q :: nat
  fixes x :: "rat mat"
  fixes xv1 :: rat
  assumes block_bound:
    "4 * Suc q ≤ 𝗏"
  shows
    "y_block_sqsum a b c d
       (brc_extend_x x xv1) q
     =
     y_block_sqsum a b c d x q"
proof -
  have b0:
    "4*q < 𝗏"
    using block_bound
    by simp

  have b1:
    "4*q + 1 < 𝗏"
    using block_bound
    by simp

  have b2:
    "4*q + 2 < 𝗏"
    using block_bound
    by simp

  have b3:
    "4*q + 3 < 𝗏"
    using block_bound
    by simp

  have e0:
    "brc_extend_x x xv1 $$ (4*q,0) =
     x $$ (4*q,0)"
    using b0
    unfolding brc_extend_x_def
    by simp

  have e1:
    "brc_extend_x x xv1 $$ (4*q+1,0) =
     x $$ (4*q+1,0)"
    using b1
    unfolding brc_extend_x_def
    by simp

  have e2:
    "brc_extend_x x xv1 $$ (4*q+2,0) =
     x $$ (4*q+2,0)"
    using b2
    unfolding brc_extend_x_def
    by simp

  have e3:
    "brc_extend_x x xv1 $$ (4*q+3,0) =
     x $$ (4*q+3,0)"
    using b3
    unfolding brc_extend_x_def
    by simp

  show ?thesis
    unfolding y_block_sqsum_def
    using e0 e1 e2 e3
    by simp
qed

lemma brc_minus_affine_match_extended_update_exists:
  fixes a b c d q :: nat
  fixes x :: "rat mat"
  fixes xv1 :: rat
  assumes nzsum:
    "a^2 + b^2 + c^2 + d^2 ≠ 0"
  assumes block_bound:
    "4 * Suc q ≤ 𝗏"
  shows
    "∃x' y0 y1 y2 y3.
       brc_minus_affine_match
         a b c d x xv1 q y0 y1 y2 y3 ∧
       (∀i. i < 4*q ⟶ i < 𝗏 ⟶
          x' $$ (i,0) = x $$ (i,0)) ∧
       y_block_sqsum a b c d
         (brc_extend_x x' xv1) q =
         y0^2 + y1^2 + y2^2 + y3^2"
proof -
  obtain x' y0 y1 y2 y3 where match:
    "brc_minus_affine_match
       a b c d x xv1 q y0 y1 y2 y3"
    and preserve:
    "∀i. i < 4*q ⟶ i < 𝗏 ⟶
       x' $$ (i,0) = x $$ (i,0)"
    and block_sum:
    "y_block_sqsum a b c d x' q =
       y0^2 + y1^2 + y2^2 + y3^2"
    using brc_minus_affine_match_update_exists[
      OF nzsum block_bound, of x xv1]
    by blast

  have extended:
    "y_block_sqsum a b c d
       (brc_extend_x x' xv1) q =
     y_block_sqsum a b c d x' q"
    using brc_extend_x_y_block_below[
      OF block_bound, of a b c d x' xv1]
    .

  have extended_sum:
    "y_block_sqsum a b c d
       (brc_extend_x x' xv1) q =
       y0^2 + y1^2 + y2^2 + y3^2"
    using extended block_sum
    by simp

  show ?thesis
    using match preserve extended_sum
    by blast
qed

lemma brc_linear_tail_update_block:
  fixes a b c d q i :: nat
  fixes x :: "rat mat"
  fixes xv1 x0 x1 x2 x3 :: rat
  assumes block_bound:
    "4 * Suc q ≤ 𝗏"
  shows
    "brc_linear_tail
       (brc_extend_x
         (update_x_block x q x0 x1 x2 x3) xv1)
       (4 * Suc q) i
     =
     brc_linear_tail
       (brc_extend_x x xv1)
       (4 * Suc q) i"
proof -
  let ?x' = "update_x_block x q x0 x1 x2 x3"
  let ?m = "4 * Suc q"

  have entry_equal:
    "brc_extend_x ?x' xv1 $$ (?m-h-1,0) =
     brc_extend_x x xv1 $$ (?m-h-1,0)"
    if h_mem:
      "h ∈ {4..< ?m}"
    for h
  proof -
    have h_ge:
      "4 ≤ h"
      using h_mem
      by simp

    have h_lt:
      "h < ?m"
      using h_mem
      by simp

    have index_before:
      "?m-h-1 < 4*q"
      using h_ge h_lt
      by simp

    have index_v:
      "?m-h-1 < 𝗏"
      using index_before block_bound
      by simp

    have updated:
      "?x' $$ (?m-h-1,0) =
       x $$ (?m-h-1,0)"
      using update_x_block_preserve_before[
        OF index_before index_v,
        of x x0 x1 x2 x3]
      .

    show ?thesis
      using updated index_v
      unfolding brc_extend_x_def
      by simp
  qed

  show ?thesis
    unfolding brc_linear_tail_def
    using entry_equal
    by (intro sum.cong) auto
qed

lemma brc_extend_x_y_of_block_below:
  fixes a b c d q :: nat
  fixes x :: "rat mat"
  fixes xv1 :: rat
  assumes block_bound:
    "4 * Suc q ≤ 𝗏"
  shows
    "y_of
       ((a,b,c,d),
        (brc_extend_x x xv1 $$ (4*q,0),
         brc_extend_x x xv1 $$ (4*q+1,0),
         brc_extend_x x xv1 $$ (4*q+2,0),
         brc_extend_x x xv1 $$ (4*q+3,0)))
     =
     y_of
       ((a,b,c,d),
        (x $$ (4*q,0),
         x $$ (4*q+1,0),
         x $$ (4*q+2,0),
         x $$ (4*q+3,0)))"
proof -
  have b0:
    "4*q < 𝗏"
    using block_bound
    by simp

  have b1:
    "4*q + 1 < 𝗏"
    using block_bound
    by simp

  have b2:
    "4*q + 2 < 𝗏"
    using block_bound
    by simp

  have b3:
    "4*q + 3 < 𝗏"
    using block_bound
    by simp

  have e0:
    "brc_extend_x x xv1 $$ (4*q,0) =
     x $$ (4*q,0)"
    using b0
    unfolding brc_extend_x_def
    by simp

  have e1:
    "brc_extend_x x xv1 $$ (4*q+1,0) =
     x $$ (4*q+1,0)"
    using b1
    unfolding brc_extend_x_def
    by simp

  have e2:
    "brc_extend_x x xv1 $$ (4*q+2,0) =
     x $$ (4*q+2,0)"
    using b2
    unfolding brc_extend_x_def
    by simp

  have e3:
    "brc_extend_x x xv1 $$ (4*q+3,0) =
     x $$ (4*q+3,0)"
    using b3
    unfolding brc_extend_x_def
    by simp

  show ?thesis
    using e0 e1 e2 e3
    by simp
qed

lemma brc_minus_affine_match_strong_update_exists:
  fixes a b c d q :: nat
  fixes x :: "rat mat"
  fixes xv1 :: rat
  assumes nzsum:
    "a^2 + b^2 + c^2 + d^2 ≠ 0"
  assumes block_bound:
    "4 * Suc q ≤ 𝗏"
  shows
    "∃x' y0 y1 y2 y3.
       brc_minus_affine_match
         a b c d x xv1 q y0 y1 y2 y3 ∧
       (∀i. i < 4*q ⟶ i < 𝗏 ⟶
          x' $$ (i,0) = x $$ (i,0)) ∧
       y_of
         ((a,b,c,d),
          (brc_extend_x x' xv1 $$ (4*q,0),
           brc_extend_x x' xv1 $$ (4*q+1,0),
           brc_extend_x x' xv1 $$ (4*q+2,0),
           brc_extend_x x' xv1 $$ (4*q+3,0)))
       =
       (y0,y1,y2,y3)"
proof -
  obtain y0 y1 y2 y3 :: rat where match:
    "brc_minus_affine_match
       a b c d x xv1 q y0 y1 y2 y3"
    using brc_minus_affine_match_exists[
      of a b c d x xv1 q]
    by blast

  have b0:
    "4*q < 𝗏"
    using block_bound
    by simp

  have b1:
    "4*q + 1 < 𝗏"
    using block_bound
    by simp

  have b2:
    "4*q + 2 < 𝗏"
    using block_bound
    by simp

  have b3:
    "4*q + 3 < 𝗏"
    using block_bound
    by simp

  let ?x0 =
    "one_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"

  let ?x1 =
    "two_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"

  let ?x2 =
    "three_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"

  let ?x3 =
    "four_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"

  let ?x' =
    "update_x_block x q ?x0 ?x1 ?x2 ?x3"

  have preserve:
    "∀i. i < 4*q ⟶ i < 𝗏 ⟶
       ?x' $$ (i,0) = x $$ (i,0)"
  proof (intro allI impI)
    fix i
    assume conditions:
      "i < 4*q"
      "i < 𝗏"

    show "?x' $$ (i,0) = x $$ (i,0)"
      using update_x_block_preserve_before[
        OF conditions, of x ?x0 ?x1 ?x2 ?x3]
      .
  qed

  have base_tuple:
    "y_of
       ((a,b,c,d),
        (?x' $$ (4*q,0),
         ?x' $$ (4*q+1,0),
         ?x' $$ (4*q+2,0),
         ?x' $$ (4*q+3,0)))
     =
     (y0,y1,y2,y3)"
    using update_x_block_y_inv_entries[
      OF nzsum b0 b1 b2 b3,
      of x y0 y1 y2 y3]
    by simp

  have extend_tuple:
    "y_of
       ((a,b,c,d),
        (brc_extend_x ?x' xv1 $$ (4*q,0),
         brc_extend_x ?x' xv1 $$ (4*q+1,0),
         brc_extend_x ?x' xv1 $$ (4*q+2,0),
         brc_extend_x ?x' xv1 $$ (4*q+3,0)))
     =
     y_of
       ((a,b,c,d),
        (?x' $$ (4*q,0),
         ?x' $$ (4*q+1,0),
         ?x' $$ (4*q+2,0),
         ?x' $$ (4*q+3,0)))"
    using brc_extend_x_y_of_block_below[
      OF block_bound, of a b c d ?x' xv1]
    .

  have tuple:
    "y_of
       ((a,b,c,d),
        (brc_extend_x ?x' xv1 $$ (4*q,0),
         brc_extend_x ?x' xv1 $$ (4*q+1,0),
         brc_extend_x ?x' xv1 $$ (4*q+2,0),
         brc_extend_x ?x' xv1 $$ (4*q+3,0)))
     =
     (y0,y1,y2,y3)"
    using extend_tuple base_tuple
    by simp

  show ?thesis
    using match preserve tuple
    by blast
qed

lemma brc_linear_tail_preserve_before:
  fixes q i :: nat
  fixes x x' :: "rat mat"
  fixes xv1 :: rat
  assumes block_bound:
    "4 * Suc q ≤ 𝗏"
  assumes preserve:
    "∀k. k < 4*q ⟶ k < 𝗏 ⟶
       x' $$ (k,0) = x $$ (k,0)"
  shows
    "brc_linear_tail
       (brc_extend_x x' xv1) (4 * Suc q) i
     =
     brc_linear_tail
       (brc_extend_x x xv1) (4 * Suc q) i"
proof -
  let ?m = "4 * Suc q"

  have entry_equal:
    "brc_extend_x x' xv1 $$ (?m-h-1,0) =
     brc_extend_x x xv1 $$ (?m-h-1,0)"
    if h_mem:
      "h ∈ {4..< ?m}"
    for h
  proof -
    have h_ge:
      "4 ≤ h"
      using h_mem
      by simp

    have h_lt:
      "h < ?m"
      using h_mem
      by simp

    have index_before:
      "?m-h-1 < 4*q"
      using h_ge h_lt
      by simp

    have index_v:
      "?m-h-1 < 𝗏"
      using index_before block_bound
      by simp

    have xx:
      "x' $$ (?m-h-1,0) =
       x $$ (?m-h-1,0)"
      using preserve index_before index_v
      by blast

    show ?thesis
      using xx index_v
      unfolding brc_extend_x_def
      by simp
  qed

  show ?thesis
    unfolding brc_linear_tail_def
    using entry_equal
    by (intro sum.cong) auto
qed

lemma brc_minus_updated_linear_form:
  fixes a b c d q i :: nat
  fixes x x' :: "rat mat"
  fixes xv1 y0 y1 y2 y3 :: rat
  assumes four_sq:
    "a^2 + b^2 + c^2 + d^2 = 𝗄 - Λ"
  assumes block_bound:
    "4 * Suc q ≤ 𝗏"
  assumes i4:
    "i < 4"
  assumes preserve:
    "∀k. k < 4*q ⟶ k < 𝗏 ⟶
       x' $$ (k,0) = x $$ (k,0)"
  assumes tuple:
    "y_of
       ((a,b,c,d),
        (brc_extend_x x' xv1 $$ (4*q,0),
         brc_extend_x x' xv1 $$ (4*q+1,0),
         brc_extend_x x' xv1 $$ (4*q+2,0),
         brc_extend_x x' xv1 $$ (4*q+3,0)))
     =
     (y0,y1,y2,y3)"
  shows
    "(∑r∈{0..<4 * Suc q}.
       of_int
         (N $$ (4 * Suc q-r-1,
                 4 * Suc q-i-1)) *
       brc_extend_x x' xv1 $$ (4 * Suc q-r-1,0))
     =
       brc_linear_coeff a b c d (4 * Suc q) i 0 * y0 +
       brc_linear_coeff a b c d (4 * Suc q) i 1 * y1 +
       brc_linear_coeff a b c d (4 * Suc q) i 2 * y2 +
       brc_linear_coeff a b c d (4 * Suc q) i 3 * y3 +
       brc_linear_tail
         (brc_extend_x x xv1) (4 * Suc q) i"
proof -
  have base:
    "(∑r∈{0..<4 * Suc q}.
       of_int
         (N $$ (4 * Suc q-r-1,
                 4 * Suc q-i-1)) *
       brc_extend_x x' xv1 $$ (4 * Suc q-r-1,0))
     =
       brc_linear_coeff a b c d (4 * Suc q) i 0 *
         one_of
           (y_of
             ((a,b,c,d),
              (brc_extend_x x' xv1 $$ (4*q,0),
               brc_extend_x x' xv1 $$ (4*q+1,0),
               brc_extend_x x' xv1 $$ (4*q+2,0),
               brc_extend_x x' xv1 $$ (4*q+3,0)))) +
       brc_linear_coeff a b c d (4 * Suc q) i 1 *
         two_of
           (y_of
             ((a,b,c,d),
              (brc_extend_x x' xv1 $$ (4*q,0),
               brc_extend_x x' xv1 $$ (4*q+1,0),
               brc_extend_x x' xv1 $$ (4*q+2,0),
               brc_extend_x x' xv1 $$ (4*q+3,0)))) +
       brc_linear_coeff a b c d (4 * Suc q) i 2 *
         three_of
           (y_of
             ((a,b,c,d),
              (brc_extend_x x' xv1 $$ (4*q,0),
               brc_extend_x x' xv1 $$ (4*q+1,0),
               brc_extend_x x' xv1 $$ (4*q+2,0),
               brc_extend_x x' xv1 $$ (4*q+3,0)))) +
       brc_linear_coeff a b c d (4 * Suc q) i 3 *
         four_of
           (y_of
             ((a,b,c,d),
              (brc_extend_x x' xv1 $$ (4*q,0),
               brc_extend_x x' xv1 $$ (4*q+1,0),
               brc_extend_x x' xv1 $$ (4*q+2,0),
               brc_extend_x x' xv1 $$ (4*q+3,0)))) +
       brc_linear_tail
         (brc_extend_x x' xv1) (4 * Suc q) i"
    using brc_minus_extended_block_linear_explicit[
      OF four_sq block_bound i4,
      of x' xv1]
    .

  have tail:
    "brc_linear_tail
       (brc_extend_x x' xv1) (4 * Suc q) i
     =
     brc_linear_tail
       (brc_extend_x x xv1) (4 * Suc q) i"
    using brc_linear_tail_preserve_before[
      OF block_bound preserve]
    .

  have y0_eq:
    "one_of
       (y_of
         ((a,b,c,d),
          (brc_extend_x x' xv1 $$ (4*q,0),
           brc_extend_x x' xv1 $$ (4*q+1,0),
           brc_extend_x x' xv1 $$ (4*q+2,0),
           brc_extend_x x' xv1 $$ (4*q+3,0))))
     = y0"
    using tuple
    by simp

  have y1_eq:
    "two_of
       (y_of
         ((a,b,c,d),
          (brc_extend_x x' xv1 $$ (4*q,0),
           brc_extend_x x' xv1 $$ (4*q+1,0),
           brc_extend_x x' xv1 $$ (4*q+2,0),
           brc_extend_x x' xv1 $$ (4*q+3,0))))
     = y1"
    using tuple
    by simp

  have y2_eq:
    "three_of
       (y_of
         ((a,b,c,d),
          (brc_extend_x x' xv1 $$ (4*q,0),
           brc_extend_x x' xv1 $$ (4*q+1,0),
           brc_extend_x x' xv1 $$ (4*q+2,0),
           brc_extend_x x' xv1 $$ (4*q+3,0))))
     = y2"
    using tuple
    by simp

  have y3_eq:
    "four_of
       (y_of
         ((a,b,c,d),
          (brc_extend_x x' xv1 $$ (4*q,0),
           brc_extend_x x' xv1 $$ (4*q+1,0),
           brc_extend_x x' xv1 $$ (4*q+2,0),
           brc_extend_x x' xv1 $$ (4*q+3,0))))
     = y3"
    using tuple
    by simp

  show ?thesis
    using base tail y0_eq y1_eq y2_eq y3_eq
    by simp
qed

lemma brc_minus_updated_four_forms:
  fixes a b c d q :: nat
  fixes x x' :: "rat mat"
  fixes xv1 y0 y1 y2 y3 :: rat
  assumes four_sq:
    "a^2 + b^2 + c^2 + d^2 = 𝗄 - Λ"
  assumes block_bound:
    "4 * Suc q ≤ 𝗏"
  assumes preserve:
    "∀k. k < 4*q ⟶ k < 𝗏 ⟶
       x' $$ (k,0) = x $$ (k,0)"
  assumes tuple:
    "y_of
       ((a,b,c,d),
        (brc_extend_x x' xv1 $$ (4*q,0),
         brc_extend_x x' xv1 $$ (4*q+1,0),
         brc_extend_x x' xv1 $$ (4*q+2,0),
         brc_extend_x x' xv1 $$ (4*q+3,0)))
     =
     (y0,y1,y2,y3)"
  assumes match:
    "brc_minus_affine_match
       a b c d x xv1 q y0 y1 y2 y3"
  shows
    "(∑r∈{0..<4 * Suc q}.
       of_int
         (N $$ (4 * Suc q-r-1,
                 4 * Suc q-0-1)) *
       brc_extend_x x' xv1 $$ (4 * Suc q-r-1,0))^2 +
     (∑r∈{0..<4 * Suc q}.
       of_int
         (N $$ (4 * Suc q-r-1,
                 4 * Suc q-1-1)) *
       brc_extend_x x' xv1 $$ (4 * Suc q-r-1,0))^2 +
     (∑r∈{0..<4 * Suc q}.
       of_int
         (N $$ (4 * Suc q-r-1,
                 4 * Suc q-2-1)) *
       brc_extend_x x' xv1 $$ (4 * Suc q-r-1,0))^2 +
     (∑r∈{0..<4 * Suc q}.
       of_int
         (N $$ (4 * Suc q-r-1,
                 4 * Suc q-3-1)) *
       brc_extend_x x' xv1 $$ (4 * Suc q-r-1,0))^2
     =
     y0^2 + y1^2 + y2^2 + y3^2"
proof -
  have i0:
    "0 < (4::nat)"
    by simp

  have i1:
    "1 < (4::nat)"
    by simp

  have i2:
    "2 < (4::nat)"
    by simp

  have i3:
    "3 < (4::nat)"
    by simp

  have form0:
    "(∑r∈{0..<4 * Suc q}.
       of_int
         (N $$ (4 * Suc q-r-1,
                 4 * Suc q-0-1)) *
       brc_extend_x x' xv1 $$ (4 * Suc q-r-1,0))
     =
       brc_linear_coeff a b c d (4 * Suc q) 0 0 * y0 +
       brc_linear_coeff a b c d (4 * Suc q) 0 1 * y1 +
       brc_linear_coeff a b c d (4 * Suc q) 0 2 * y2 +
       brc_linear_coeff a b c d (4 * Suc q) 0 3 * y3 +
       brc_linear_tail
         (brc_extend_x x xv1) (4 * Suc q) 0"
    using brc_minus_updated_linear_form[
      OF four_sq block_bound i0 preserve tuple]
    .

  have form1:
    "(∑r∈{0..<4 * Suc q}.
       of_int
         (N $$ (4 * Suc q-r-1,
                 4 * Suc q-1-1)) *
       brc_extend_x x' xv1 $$ (4 * Suc q-r-1,0))
     =
       brc_linear_coeff a b c d (4 * Suc q) 1 0 * y0 +
       brc_linear_coeff a b c d (4 * Suc q) 1 1 * y1 +
       brc_linear_coeff a b c d (4 * Suc q) 1 2 * y2 +
       brc_linear_coeff a b c d (4 * Suc q) 1 3 * y3 +
       brc_linear_tail
         (brc_extend_x x xv1) (4 * Suc q) 1"
    using brc_minus_updated_linear_form[
      OF four_sq block_bound i1 preserve tuple]
    .

  have form2:
    "(∑r∈{0..<4 * Suc q}.
       of_int
         (N $$ (4 * Suc q-r-1,
                 4 * Suc q-2-1)) *
       brc_extend_x x' xv1 $$ (4 * Suc q-r-1,0))
     =
       brc_linear_coeff a b c d (4 * Suc q) 2 0 * y0 +
       brc_linear_coeff a b c d (4 * Suc q) 2 1 * y1 +
       brc_linear_coeff a b c d (4 * Suc q) 2 2 * y2 +
       brc_linear_coeff a b c d (4 * Suc q) 2 3 * y3 +
       brc_linear_tail
         (brc_extend_x x xv1) (4 * Suc q) 2"
    using brc_minus_updated_linear_form[
      OF four_sq block_bound i2 preserve tuple]
    .

  have form3:
    "(∑r∈{0..<4 * Suc q}.
       of_int
         (N $$ (4 * Suc q-r-1,
                 4 * Suc q-3-1)) *
       brc_extend_x x' xv1 $$ (4 * Suc q-r-1,0))
     =
       brc_linear_coeff a b c d (4 * Suc q) 3 0 * y0 +
       brc_linear_coeff a b c d (4 * Suc q) 3 1 * y1 +
       brc_linear_coeff a b c d (4 * Suc q) 3 2 * y2 +
       brc_linear_coeff a b c d (4 * Suc q) 3 3 * y3 +
       brc_linear_tail
         (brc_extend_x x xv1) (4 * Suc q) 3"
    using brc_minus_updated_linear_form[
      OF four_sq block_bound i3 preserve tuple]
    .

  have affine_sum:
    "(brc_linear_coeff a b c d (4 * Suc q) 0 0 * y0 +
      brc_linear_coeff a b c d (4 * Suc q) 0 1 * y1 +
      brc_linear_coeff a b c d (4 * Suc q) 0 2 * y2 +
      brc_linear_coeff a b c d (4 * Suc q) 0 3 * y3 +
      brc_linear_tail
        (brc_extend_x x xv1) (4 * Suc q) 0)^2 +
     (brc_linear_coeff a b c d (4 * Suc q) 1 0 * y0 +
      brc_linear_coeff a b c d (4 * Suc q) 1 1 * y1 +
      brc_linear_coeff a b c d (4 * Suc q) 1 2 * y2 +
      brc_linear_coeff a b c d (4 * Suc q) 1 3 * y3 +
      brc_linear_tail
        (brc_extend_x x xv1) (4 * Suc q) 1)^2 +
     (brc_linear_coeff a b c d (4 * Suc q) 2 0 * y0 +
      brc_linear_coeff a b c d (4 * Suc q) 2 1 * y1 +
      brc_linear_coeff a b c d (4 * Suc q) 2 2 * y2 +
      brc_linear_coeff a b c d (4 * Suc q) 2 3 * y3 +
      brc_linear_tail
        (brc_extend_x x xv1) (4 * Suc q) 2)^2 +
     (brc_linear_coeff a b c d (4 * Suc q) 3 0 * y0 +
      brc_linear_coeff a b c d (4 * Suc q) 3 1 * y1 +
      brc_linear_coeff a b c d (4 * Suc q) 3 2 * y2 +
      brc_linear_coeff a b c d (4 * Suc q) 3 3 * y3 +
      brc_linear_tail
        (brc_extend_x x xv1) (4 * Suc q) 3)^2
     =
     y0^2 + y1^2 + y2^2 + y3^2"
    using match
    unfolding brc_minus_affine_match_def
    .

  show ?thesis
    using form0 form1 form2 form3 affine_sum
    by metis
qed

lemma brc_minus_updated_local_identity:
  fixes a b c d q :: nat
  fixes x x' :: "rat mat"
  fixes xv1 y0 y1 y2 y3 :: rat
  assumes four_sq:
    "a^2 + b^2 + c^2 + d^2 = 𝗄 - Λ"
  assumes block_bound:
    "4 * Suc q ≤ 𝗏"
  assumes preserve:
    "∀k. k < 4*q ⟶ k < 𝗏 ⟶
       x' $$ (k,0) = x $$ (k,0)"
  assumes tuple:
    "y_of
       ((a,b,c,d),
        (brc_extend_x x' xv1 $$ (4*q,0),
         brc_extend_x x' xv1 $$ (4*q+1,0),
         brc_extend_x x' xv1 $$ (4*q+2,0),
         brc_extend_x x' xv1 $$ (4*q+3,0)))
     =
     (y0,y1,y2,y3)"
  assumes match:
    "brc_minus_affine_match
       a b c d x xv1 q y0 y1 y2 y3"
  shows
    "y_block_sqsum a b c d
       (brc_extend_x x' xv1) q
     =
     (∑j∈{0..<4}.
       (∑r∈{0..<4 * Suc q}.
          of_int
            (N $$ (4 * Suc q-r-1,
                    4 * Suc q-j-1)) *
          brc_extend_x x' xv1 $$
            (4 * Suc q-r-1,0))^2)"
proof -
  let ?L =
    "λj.
       (∑r∈{0..<4 * Suc q}.
          of_int
            (N $$ (4 * Suc q-r-1,
                    4 * Suc q-j-1)) *
          brc_extend_x x' xv1 $$
            (4 * Suc q-r-1,0))"

  have four_forms:
    "(?L 0)^2 + (?L 1)^2 +
     (?L 2)^2 + (?L 3)^2
     =
     y0^2 + y1^2 + y2^2 + y3^2"
    using brc_minus_updated_four_forms[
      OF four_sq block_bound preserve tuple match]
    by simp

  have sum_four:
    "(∑j∈{0..<4}. (?L j)^2)
     =
     (?L 0)^2 + (?L 1)^2 +
     (?L 2)^2 + (?L 3)^2"
    by (simp add: numeral.simps(2,3))

  have block_sum:
    "y_block_sqsum a b c d
       (brc_extend_x x' xv1) q
     =
     y0^2 + y1^2 + y2^2 + y3^2"
    unfolding y_block_sqsum_def
    using tuple
    by simp

  show ?thesis
    using block_sum four_forms sum_four
    by argo
qed

lemma brc_minus_local_step_interior:
  fixes a b c d q :: nat
  fixes xv1 :: rat
  assumes four_sq:
    "a^2 + b^2 + c^2 + d^2 = 𝗄 - Λ"
  assumes nzsum:
    "a^2 + b^2 + c^2 + d^2 ≠ 0"
  assumes next_bound:
    "4 * Suc q ≤ 𝗏"
  shows
    "brc_minus_local_step a b c d xv1 q"
proof -
  show ?thesis
    unfolding brc_minus_local_step_def
  proof (intro allI impI)
    fix x :: "rat mat"

    assume current_bound:
      "4 * q ≤ 𝗏"

    obtain x' y0 y1 y2 y3 where match:
      "brc_minus_affine_match
         a b c d x xv1 q y0 y1 y2 y3"
      and preserve:
      "∀i. i < 4*q ⟶ i < 𝗏 ⟶
         x' $$ (i,0) = x $$ (i,0)"
      and tuple:
      "y_of
         ((a,b,c,d),
          (brc_extend_x x' xv1 $$ (4*q,0),
           brc_extend_x x' xv1 $$ (4*q+1,0),
           brc_extend_x x' xv1 $$ (4*q+2,0),
           brc_extend_x x' xv1 $$ (4*q+3,0)))
       =
       (y0,y1,y2,y3)"
      using brc_minus_affine_match_strong_update_exists[
        OF nzsum next_bound, of x xv1]
      by blast

    have local:
      "y_block_sqsum a b c d
         (brc_extend_x x' xv1) q
       =
       (∑j∈{0..<4}.
         (∑r∈{0..<4 * Suc q}.
            of_int
              (N $$ (4 * Suc q-r-1,
                      4 * Suc q-j-1)) *
            brc_extend_x x' xv1 $$
              (4 * Suc q-r-1,0))^2)"
      using brc_minus_updated_local_identity[
        OF four_sq next_bound preserve tuple match]
      .

    show
      "∃x' :: rat mat.
         (∀i. i < 4*q ⟶ i < 𝗏 ⟶
              x' $$ (i,0) = x $$ (i,0)) ∧
         y_block_sqsum a b c d
           (brc_extend_x x' xv1) q
         =
         (∑j∈{0..<4}.
           (∑r∈{0..<4 * Suc q}.
              of_int
                (N $$ (4 * Suc q-r-1,
                        4 * Suc q-j-1)) *
              brc_extend_x x' xv1 $$
                (4 * Suc q-r-1,0))^2)"
      using preserve local
      by blast
  qed
qed

lemma brc_minus_interior_prefix_exists:
  fixes a b c d w :: nat
  fixes xv1 :: rat
  assumes v_form:
    "𝗏 = 4 * w - 1"
  assumes w_pos:
    "0 < w"
  assumes four_sq:
    "a^2 + b^2 + c^2 + d^2 = 𝗄 - Λ"
  assumes nzsum:
    "a^2 + b^2 + c^2 + d^2 ≠ 0"
  shows
    "∃x :: rat mat.
       brc_minus_prefix_eliminated
         a b c d x xv1 (w - 1)"
proof -
  have prefix_bound:
    "4 * (w - 1) ≤ 𝗏"
    using v_form w_pos
    by simp

  have steps:
    "∀q < w - 1.
       brc_minus_local_step a b c d xv1 q"
  proof (intro allI impI)
    fix q
    assume q_lt:
      "q < w - 1"

    have next_bound:
      "4 * Suc q ≤ 𝗏"
    proof -
      have
        "Suc q ≤ w - 1"
        using q_lt
        by simp

      then have
        "4 * Suc q ≤ 4 * (w - 1)"
        by simp

      then show ?thesis
        using prefix_bound
        by simp
    qed

    show
      "brc_minus_local_step a b c d xv1 q"
      using brc_minus_local_step_interior[
        OF four_sq nzsum next_bound]
      .
  qed

  show ?thesis
    using brc_minus_prefix_exists_upto[
      OF steps prefix_bound]
    .
qed

lemma brc_extend_x_y_block_independent:
  fixes a b c d q :: nat
  fixes x :: "rat mat"
  fixes u v :: rat
  assumes block_bound:
    "4 * Suc q ≤ 𝗏"
  shows
    "y_block_sqsum a b c d
       (brc_extend_x x u) q
     =
     y_block_sqsum a b c d
       (brc_extend_x x v) q"
proof -
  have left:
    "y_block_sqsum a b c d
       (brc_extend_x x u) q
     =
     y_block_sqsum a b c d x q"
    using brc_extend_x_y_block_below[
      OF block_bound, of a b c d x u]
    .

  have right:
    "y_block_sqsum a b c d
       (brc_extend_x x v) q
     =
     y_block_sqsum a b c d x q"
    using brc_extend_x_y_block_below[
      OF block_bound, of a b c d x v]
    .

  show ?thesis
    using left right
    by simp
qed

lemma brc_minus_prefix_independent_xv1:
  fixes a b c d q :: nat
  fixes x :: "rat mat"
  fixes u v :: rat
  assumes prefix:
    "brc_minus_prefix_eliminated
       a b c d x u q"
  assumes prefix_bound:
    "4 * q ≤ 𝗏"
  shows
    "brc_minus_prefix_eliminated
       a b c d x v q"
proof -
  show ?thesis
    unfolding brc_minus_prefix_eliminated_def
  proof (intro allI impI)
    fix t
    assume t_lt:
      "t < q"

    have block_bound:
      "4 * Suc t ≤ 𝗏"
    proof -
      have
        "Suc t ≤ q"
        using t_lt
        by simp

      then have
        "4 * Suc t ≤ 4 * q"
        by simp

      then show ?thesis
        using prefix_bound
        by simp
    qed

    have old:
      "y_block_sqsum a b c d
         (brc_extend_x x u) t
       =
       (∑j∈{0..<4}.
         (∑r∈{0..<4 * Suc t}.
           of_int
             (N $$ (4 * Suc t-r-1,
                     4 * Suc t-j-1)) *
           brc_extend_x x u $$
             (4 * Suc t-r-1,0))^2)"
      using prefix t_lt
      unfolding brc_minus_prefix_eliminated_def
      by blast

    have left:
      "y_block_sqsum a b c d
         (brc_extend_x x v) t
       =
       y_block_sqsum a b c d
         (brc_extend_x x u) t"
      using brc_extend_x_y_block_independent[
        OF block_bound, of a b c d x v u]
      .

    have entry_equal:
      "brc_extend_x x v $$ (4 * Suc t-r-1,0) =
       brc_extend_x x u $$ (4 * Suc t-r-1,0)"
      if r_mem:
        "r ∈ {0..<4 * Suc t}"
      for r
    proof -
      have index_lt:
        "4 * Suc t-r-1 < 4 * Suc t"
        using r_mem
        by simp

      have index_v:
        "4 * Suc t-r-1 < 𝗏"
        using index_lt block_bound
        by simp

      show ?thesis
        using index_v
        unfolding brc_extend_x_def
        by simp
    qed

    have right:
      "(∑j∈{0..<4}.
        (∑r∈{0..<4 * Suc t}.
          of_int
            (N $$ (4 * Suc t-r-1,
                    4 * Suc t-j-1)) *
          brc_extend_x x v $$
            (4 * Suc t-r-1,0))^2)
       =
       (∑j∈{0..<4}.
        (∑r∈{0..<4 * Suc t}.
          of_int
            (N $$ (4 * Suc t-r-1,
                    4 * Suc t-j-1)) *
          brc_extend_x x u $$
            (4 * Suc t-r-1,0))^2)"
      using entry_equal
      by (intro sum.cong) auto

    show
      "y_block_sqsum a b c d
         (brc_extend_x x v) t
       =
       (∑j∈{0..<4}.
         (∑r∈{0..<4 * Suc t}.
           of_int
             (N $$ (4 * Suc t-r-1,
                     4 * Suc t-j-1)) *
           brc_extend_x x v $$
             (4 * Suc t-r-1,0))^2)"
      using left old right
      by simp
  qed
qed

lemma brc_minus_interior_prefix_exists_all_xv1:
  fixes a b c d w :: nat
  assumes v_form:
    "𝗏 = 4 * w - 1"
  assumes w_pos:
    "0 < w"
  assumes four_sq:
    "a^2 + b^2 + c^2 + d^2 = 𝗄 - Λ"
  assumes nzsum:
    "a^2 + b^2 + c^2 + d^2 ≠ 0"
  shows
    "∃x :: rat mat.
       ∀xv1 :: rat.
         brc_minus_prefix_eliminated
           a b c d x xv1 (w - 1)"
proof -
  obtain x :: "rat mat" where prefix_zero:
    "brc_minus_prefix_eliminated
       a b c d x 0 (w - 1)"
    using brc_minus_interior_prefix_exists[
      OF v_form w_pos four_sq nzsum,
      of "0::rat"]
    by blast

  have prefix_bound:
    "4 * (w - 1) ≤ 𝗏"
    using v_form w_pos
    by simp

  have all:
    "∀xv1 :: rat.
       brc_minus_prefix_eliminated
         a b c d x xv1 (w - 1)"
  proof
    fix xv1 :: rat

    show
      "brc_minus_prefix_eliminated
         a b c d x xv1 (w - 1)"
      using brc_minus_prefix_independent_xv1[
        OF prefix_zero prefix_bound,
        of xv1]
      .
  qed

  show ?thesis
    using all
    by blast
qed

lemma brc_linear_block_explicit_general:
  fixes a b c d m i :: nat
  fixes x :: "rat mat"
  assumes four_sq:
    "a^2 + b^2 + c^2 + d^2 = 𝗄 - Λ"
  assumes m_gt3:
    "3 < m"
  assumes i4:
    "i < 4"
  shows
    "(∑r∈{0..<m}.
       of_int
         (N $$ (m-r-1,m-i-1)) *
       x $$ (m-r-1,0))
     =
       brc_linear_coeff a b c d m i 0 *
         one_of
           (y_of
             ((a,b,c,d),
              (x $$ (m-4,0),
               x $$ (m-3,0),
               x $$ (m-2,0),
               x $$ (m-1,0)))) +
       brc_linear_coeff a b c d m i 1 *
         two_of
           (y_of
             ((a,b,c,d),
              (x $$ (m-4,0),
               x $$ (m-3,0),
               x $$ (m-2,0),
               x $$ (m-1,0)))) +
       brc_linear_coeff a b c d m i 2 *
         three_of
           (y_of
             ((a,b,c,d),
              (x $$ (m-4,0),
               x $$ (m-3,0),
               x $$ (m-2,0),
               x $$ (m-1,0)))) +
       brc_linear_coeff a b c d m i 3 *
         four_of
           (y_of
             ((a,b,c,d),
              (x $$ (m-4,0),
               x $$ (m-3,0),
               x $$ (m-2,0),
               x $$ (m-1,0)))) +
       brc_linear_tail x m i"
proof -
  have i_mem:
    "i ∈ {0..<4}"
    using i4
    by simp

  have x0:
    "x $$ (m-4,0) = x $$ (m-4,0)"
    by simp

  have x1:
    "x $$ (m-3,0) = x $$ (m-3,0)"
    by simp

  have x2:
    "x $$ (m-2,0) = x $$ (m-2,0)"
    by simp

  have x3:
    "x $$ (m-1,0) = x $$ (m-1,0)"
    by simp

  show ?thesis
    using linear_comb_of_y_explicit[
      OF four_sq m_gt3 i_mem x0 x1 x2 x3]
    .
qed

lemma brc_terminal_linear_form:
  fixes a b c d w i :: nat
  fixes x :: "rat mat"
  fixes xv1 :: rat
  assumes v_form:
    "𝗏 = 4 * w - 1"
  assumes w_pos:
    "0 < w"
  assumes four_sq:
    "a^2 + b^2 + c^2 + d^2 = 𝗄 - Λ"
  assumes i4:
    "i < 4"
  shows
    "(∑r∈{0..<𝗏 + 1}.
       of_int
         (N $$ (𝗏 + 1-r-1,
                 𝗏 + 1-i-1)) *
       brc_extend_x x xv1 $$ (𝗏 + 1-r-1,0))
     =
       brc_linear_coeff a b c d (𝗏 + 1) i 0 *
         one_of
           (y_of
             ((a,b,c,d),
              (x $$ (𝗏-3,0),
               x $$ (𝗏-2,0),
               x $$ (𝗏-1,0),
               xv1))) +
       brc_linear_coeff a b c d (𝗏 + 1) i 1 *
         two_of
           (y_of
             ((a,b,c,d),
              (x $$ (𝗏-3,0),
               x $$ (𝗏-2,0),
               x $$ (𝗏-1,0),
               xv1))) +
       brc_linear_coeff a b c d (𝗏 + 1) i 2 *
         three_of
           (y_of
             ((a,b,c,d),
              (x $$ (𝗏-3,0),
               x $$ (𝗏-2,0),
               x $$ (𝗏-1,0),
               xv1))) +
       brc_linear_coeff a b c d (𝗏 + 1) i 3 *
         four_of
           (y_of
             ((a,b,c,d),
              (x $$ (𝗏-3,0),
               x $$ (𝗏-2,0),
               x $$ (𝗏-1,0),
               xv1))) +
       brc_linear_tail
         (brc_extend_x x xv1) (𝗏 + 1) i"
proof -
  have m_gt3:
    "3 < 𝗏 + 1"
    using v_form w_pos
    by simp

  have e0:
    "brc_extend_x x xv1 $$ (𝗏 + 1-4,0) =
     x $$ (𝗏-3,0)"
  proof -
    have v3:
      "𝗏 - 3 < 𝗏"
      using v_form w_pos
      by simp

    show ?thesis
      using brc_extend_x_old[
        OF v3, of x xv1]
      by simp
  qed

  have e1:
    "brc_extend_x x xv1 $$ (𝗏 + 1-3,0) =
     x $$ (𝗏-2,0)"
  proof -
    have v2:
      "𝗏 - 2 < 𝗏"
      using v_form w_pos
      by simp

    show ?thesis
      using brc_extend_x_old[
        OF v2, of x xv1]
      by simp
  qed

  have e2:
    "brc_extend_x x xv1 $$ (𝗏 + 1-2,0) =
     x $$ (𝗏-1,0)"
  proof -
    have v1:
      "𝗏 - 1 < 𝗏"
      using v_form w_pos
      by simp

    show ?thesis
      using brc_extend_x_old[
        OF v1, of x xv1]
      by simp
  qed

  have e3:
    "brc_extend_x x xv1 $$ (𝗏 + 1-1,0) =
     xv1"
    using brc_extend_x_last[
      of x xv1]
    by simp

  have base:
    "(∑r∈{0..<𝗏 + 1}.
       of_int
         (N $$ (𝗏 + 1-r-1,
                 𝗏 + 1-i-1)) *
       brc_extend_x x xv1 $$ (𝗏 + 1-r-1,0))
     =
       brc_linear_coeff a b c d (𝗏 + 1) i 0 *
         one_of
           (y_of
             ((a,b,c,d),
              (brc_extend_x x xv1 $$ (𝗏 + 1-4,0),
               brc_extend_x x xv1 $$ (𝗏 + 1-3,0),
               brc_extend_x x xv1 $$ (𝗏 + 1-2,0),
               brc_extend_x x xv1 $$ (𝗏 + 1-1,0)))) +
       brc_linear_coeff a b c d (𝗏 + 1) i 1 *
         two_of
           (y_of
             ((a,b,c,d),
              (brc_extend_x x xv1 $$ (𝗏 + 1-4,0),
               brc_extend_x x xv1 $$ (𝗏 + 1-3,0),
               brc_extend_x x xv1 $$ (𝗏 + 1-2,0),
               brc_extend_x x xv1 $$ (𝗏 + 1-1,0)))) +
       brc_linear_coeff a b c d (𝗏 + 1) i 2 *
         three_of
           (y_of
             ((a,b,c,d),
              (brc_extend_x x xv1 $$ (𝗏 + 1-4,0),
               brc_extend_x x xv1 $$ (𝗏 + 1-3,0),
               brc_extend_x x xv1 $$ (𝗏 + 1-2,0),
               brc_extend_x x xv1 $$ (𝗏 + 1-1,0)))) +
       brc_linear_coeff a b c d (𝗏 + 1) i 3 *
         four_of
           (y_of
             ((a,b,c,d),
              (brc_extend_x x xv1 $$ (𝗏 + 1-4,0),
               brc_extend_x x xv1 $$ (𝗏 + 1-3,0),
               brc_extend_x x xv1 $$ (𝗏 + 1-2,0),
               brc_extend_x x xv1 $$ (𝗏 + 1-1,0)))) +
       brc_linear_tail
         (brc_extend_x x xv1) (𝗏 + 1) i"
    using brc_linear_block_explicit_general[
      OF four_sq m_gt3 i4,
      of "brc_extend_x x xv1"]
    .

  show ?thesis
    using base e0 e1 e2 e3
    by simp
qed

definition brc_terminal_form ::
  "rat mat ⇒ nat ⇒ rat" where
  "brc_terminal_form x i =
     (∑h∈{0..<𝗏}.
        of_int (N $$ (h,i)) * x $$ (h,0))"

lemma brc_terminal_form_eq_L:
  "brc_terminal_form x i = brc_L x i"
  unfolding brc_terminal_form_def brc_L_def
  by simp

lemma sum_last_three:
  fixes f :: "nat ⇒ rat"
  assumes m3:
    "3 ≤ m"
  shows
    "(∑j = m - 3..<m. f j)
     =
     f (m - 3) +
     f (m - 2) +
     f (m - 1)"
proof -
  have a1:
    "Suc (m - 3) = m - 2"
    using m3
    by simp

  have a2:
    "Suc (Suc (m - 3)) = m - 1"
    using m3
    by simp

  have
    "(∑j = m - 3..<m. f j)
     =
     f (m - 3) +
     f (Suc (m - 3)) +
     f (Suc (Suc (m - 3)))"
    using m3
    by (subst sum.atLeast_Suc_lessThan, simp_all)+

  then show ?thesis
    using a1 a2
    by simp
qed

lemma brc_terminal_form_split_last_three:
  fixes x :: "rat mat"
  fixes i :: nat
  assumes v3:
    "3 ≤ 𝗏"
  shows
    "brc_L x i
     =
     (∑h∈{0..<𝗏 - 3}.
        of_int (N $$ (h,i)) * x $$ (h,0))
     +
     of_int (N $$ (𝗏 - 3,i)) * x $$ (𝗏 - 3,0)
     +
     of_int (N $$ (𝗏 - 2,i)) * x $$ (𝗏 - 2,0)
     +
     of_int (N $$ (𝗏 - 1,i)) * x $$ (𝗏 - 1,0)"
proof -
  let ?f =
    "λh. of_int (N $$ (h,i)) * x $$ (h,0)"

  have split:
    "(∑h∈{0..<𝗏}. ?f h)
     =
     (∑h∈{0..<𝗏 - 3}. ?f h) +
     (∑h∈{𝗏 - 3..<𝗏}. ?f h)"
    using v3
    by (simp add: sum.atLeastLessThan_concat)

  have last_three:
    "(∑h∈{𝗏 - 3..<𝗏}. ?f h)
     =
     ?f (𝗏 - 3) +
     ?f (𝗏 - 2) +
     ?f (𝗏 - 1)"
    using sum_last_three[
      OF v3, of ?f]
    .

  show ?thesis
    unfolding brc_L_def
    using split last_three
    by simp
qed

lemma brc_terminal_update_from_y:
  fixes a b c d w :: nat
  fixes x :: "rat mat"
  fixes y0 y1 y2 y3 :: rat
  assumes v_form:
    "𝗏 = 4 * w - 1"
  assumes w_pos:
    "0 < w"
  assumes nzsum:
    "a^2 + b^2 + c^2 + d^2 ≠ 0"
  shows
    "∃x' xv1.
       (∀i. i < 𝗏 - 3 ⟶ i < 𝗏 ⟶
          x' $$ (i,0) = x $$ (i,0)) ∧
       y_of
         ((a,b,c,d),
          (brc_extend_x x' xv1 $$ (𝗏-3,0),
           brc_extend_x x' xv1 $$ (𝗏-2,0),
           brc_extend_x x' xv1 $$ (𝗏-1,0),
           brc_extend_x x' xv1 $$ (𝗏,0)))
       =
       (y0,y1,y2,y3)"
proof -
  let ?h = "w - 1"

  let ?x0 =
    "one_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"

  let ?x1 =
    "two_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"

  let ?x2 =
    "three_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"

  let ?x3 =
    "four_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"

  let ?x' =
    "update_x_block x ?h ?x0 ?x1 ?x2 ?x3"

  have h0:
    "4 * ?h = 𝗏 - 3"
    using v_form w_pos
    by simp

  have h1:
    "4 * ?h + 1 = 𝗏 - 2"
    using v_form w_pos
    by simp

  have h2:
    "4 * ?h + 2 = 𝗏 - 1"
    using v_form w_pos
    by simp

  have b0:
    "4 * ?h < 𝗏"
    using h0 v_form w_pos
    by simp

  have b1:
    "4 * ?h + 1 < 𝗏"
    using h1 v_form w_pos
    by simp

  have b2:
    "4 * ?h + 2 < 𝗏"
    using h2 v_form w_pos
    by simp

  have preserve:
    "∀i. i < 𝗏 - 3 ⟶ i < 𝗏 ⟶
       ?x' $$ (i,0) = x $$ (i,0)"
  proof (intro allI impI)
    fix i
    assume conditions:
      "i < 𝗏 - 3"
      "i < 𝗏"

    have i_block:
      "i < 4 * ?h"
      using conditions(1) h0
      by simp

    show "?x' $$ (i,0) = x $$ (i,0)"
      using update_x_block_preserve_before[
        OF i_block conditions(2),
        of x ?x0 ?x1 ?x2 ?x3]
      .
  qed

  have e0:
    "?x' $$ (𝗏-3,0) = ?x0"
    using update_x_block_0[
      OF b0, of x ?x0 ?x1 ?x2 ?x3]
      h0
    by simp

  have e1:
    "?x' $$ (𝗏-2,0) = ?x1"
    using update_x_block_1[
      OF b1, of x ?x0 ?x1 ?x2 ?x3]
      h1
    by simp

  have e2:
    "?x' $$ (𝗏-1,0) = ?x2"
    using update_x_block_2[
      OF b2, of x ?x0 ?x1 ?x2 ?x3]
      h2
    by simp

  have old0:
    "brc_extend_x ?x' ?x3 $$ (𝗏-3,0) = ?x0"
  proof -
    have "𝗏 - 3 < 𝗏"
      using v_form w_pos
      by simp

    then show ?thesis
      using e0
      unfolding brc_extend_x_def
      by simp
  qed

  have old1:
    "brc_extend_x ?x' ?x3 $$ (𝗏-2,0) = ?x1"
  proof -
    have "𝗏 - 2 < 𝗏"
      using v_form w_pos
      by simp

    then show ?thesis
      using e1
      unfolding brc_extend_x_def
      by simp
  qed

  have old2:
    "brc_extend_x ?x' ?x3 $$ (𝗏-1,0) = ?x2"
  proof -
    have "𝗏 - 1 < 𝗏"
      using v_form w_pos
      by simp

    then show ?thesis
      using e2
      unfolding brc_extend_x_def
      by simp
  qed

  have last:
    "brc_extend_x ?x' ?x3 $$ (𝗏,0) = ?x3"
    using brc_extend_x_last[
      of ?x' ?x3]
    .

  have inv:
    "y_reversible
       (y_inv_reversible ((a,b,c,d),(y0,y1,y2,y3)))
     =
     ((a,b,c,d),(y0,y1,y2,y3))"
    using y_inverses_part_2[
      OF nzsum, of y0 y1 y2 y3]
    .

  have tuple:
    "y_of
       ((a,b,c,d),
        (brc_extend_x ?x' ?x3 $$ (𝗏-3,0),
         brc_extend_x ?x' ?x3 $$ (𝗏-2,0),
         brc_extend_x ?x' ?x3 $$ (𝗏-1,0),
         brc_extend_x ?x' ?x3 $$ (𝗏,0)))
     =
     (y0,y1,y2,y3)"
    using old0 old1 old2 last inv
    by simp

  show ?thesis
    using preserve tuple
    by blast
qed

definition brc_terminal_tail ::
  "rat mat ⇒ nat ⇒ rat" where
  "brc_terminal_tail x i =
     (∑h∈{0..<𝗏 - 3}.
        of_int (N $$ (h,i)) * x $$ (h,0))"

definition brc_terminal_coeff ::
  "nat ⇒ nat ⇒ nat ⇒ nat ⇒ nat ⇒ nat ⇒ rat" where
  "brc_terminal_coeff a b c d i j =
     (let D =
        of_nat (a^2 + b^2 + c^2 + d^2) :: rat;
          n0 = of_int (N $$ (𝗏-3,i));
          n1 = of_int (N $$ (𝗏-2,i));
          n2 = of_int (N $$ (𝗏-1,i))
      in
        if j = 0 then
          n0 * of_nat a / D +
          n1 * of_nat b / D +
          n2 * of_nat c / D
        else if j = 1 then
          - n0 * of_nat b / D +
            n1 * of_nat a / D -
            n2 * of_nat d / D
        else if j = 2 then
          - n0 * of_nat c / D +
            n1 * of_nat d / D +
            n2 * of_nat a / D
        else
          - n0 * of_nat d / D -
            n1 * of_nat c / D +
            n2 * of_nat b / D)"

lemma brc_terminal_tuple_inverse_entries:
  fixes a b c d :: nat
  fixes x :: "rat mat"
  fixes xv1 y0 y1 y2 y3 :: rat
  assumes nzsum:
    "a^2 + b^2 + c^2 + d^2 ≠ 0"
  assumes tuple:
    "y_of
       ((a,b,c,d),
        (brc_extend_x x xv1 $$ (𝗏-3,0),
         brc_extend_x x xv1 $$ (𝗏-2,0),
         brc_extend_x x xv1 $$ (𝗏-1,0),
         brc_extend_x x xv1 $$ (𝗏,0)))
     =
     (y0,y1,y2,y3)"
  shows
    "brc_extend_x x xv1 $$ (𝗏-3,0) =
       one_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3))) ∧
     brc_extend_x x xv1 $$ (𝗏-2,0) =
       two_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3))) ∧
     brc_extend_x x xv1 $$ (𝗏-1,0) =
       three_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3))) ∧
     brc_extend_x x xv1 $$ (𝗏,0) =
       four_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
proof -
  let ?z0 = "brc_extend_x x xv1 $$ (𝗏-3,0)"
  let ?z1 = "brc_extend_x x xv1 $$ (𝗏-2,0)"
  let ?z2 = "brc_extend_x x xv1 $$ (𝗏-1,0)"
  let ?z3 = "brc_extend_x x xv1 $$ (𝗏,0)"

  have forward:
    "y_reversible
       ((a,b,c,d),(?z0,?z1,?z2,?z3))
     =
     ((a,b,c,d),(y0,y1,y2,y3))"
    using tuple
    by simp

  have inverse_left:
    "y_inv_reversible
       (y_reversible
         ((a,b,c,d),(?z0,?z1,?z2,?z3)))
     =
     ((a,b,c,d),(?z0,?z1,?z2,?z3))"
    using y_inverses_part_1[
      OF nzsum, of ?z0 ?z1 ?z2 ?z3]
    .

  have inverse:
    "y_inv_reversible
       ((a,b,c,d),(y0,y1,y2,y3))
     =
     ((a,b,c,d),(?z0,?z1,?z2,?z3))"
    using forward inverse_left
    by metis

  have e0:
    "?z0 =
     one_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
    using inverse
    by simp

  have e1:
    "?z1 =
     two_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
    using inverse
    by simp

  have e2:
    "?z2 =
     three_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
    using inverse
    by simp

  have e3:
    "?z3 =
     four_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
    using inverse
    by simp

  show ?thesis
    using e0 e1 e2 e3
    by blast
qed

lemma brc_terminal_tail_preserve:
  fixes x x' :: "rat mat"
  fixes i :: nat
  assumes preserve:
    "∀h. h < 𝗏 - 3 ⟶ h < 𝗏 ⟶
       x' $$ (h,0) = x $$ (h,0)"
  shows
    "brc_terminal_tail x' i =
     brc_terminal_tail x i"
proof -
  have entry_equal:
    "of_int (N $$ (h,i)) * x' $$ (h,0) =
     of_int (N $$ (h,i)) * x $$ (h,0)"
    if h_mem:
      "h ∈ {0..<𝗏 - 3}"
    for h
  proof -
    have h_before:
      "h < 𝗏 - 3"
      using h_mem
      by simp

    have h_v:
      "h < 𝗏"
      using h_before
      by simp

    have xx:
      "x' $$ (h,0) = x $$ (h,0)"
      using preserve h_before h_v
      by blast

    show ?thesis
      using xx
      by simp
  qed

  show ?thesis
    unfolding brc_terminal_tail_def
    using entry_equal
    by (intro sum.cong) auto
qed

lemma brc_terminal_coeff_0:
  "brc_terminal_coeff a b c d i 0 =
    (let D =
       of_nat (a^2 + b^2 + c^2 + d^2) :: rat;
         n0 = of_int (N $$ (𝗏-3,i));
         n1 = of_int (N $$ (𝗏-2,i));
         n2 = of_int (N $$ (𝗏-1,i))
     in
       n0 * of_nat a / D +
       n1 * of_nat b / D +
       n2 * of_nat c / D)"
  unfolding brc_terminal_coeff_def
  by simp

lemma brc_terminal_coeff_1:
  "brc_terminal_coeff a b c d i 1 =
    (let D =
       of_nat (a^2 + b^2 + c^2 + d^2) :: rat;
         n0 = of_int (N $$ (𝗏-3,i));
         n1 = of_int (N $$ (𝗏-2,i));
         n2 = of_int (N $$ (𝗏-1,i))
     in
       - n0 * of_nat b / D +
         n1 * of_nat a / D -
         n2 * of_nat d / D)"
  unfolding brc_terminal_coeff_def
  by simp

lemma brc_terminal_coeff_2:
  "brc_terminal_coeff a b c d i 2 =
    (let D =
       of_nat (a^2 + b^2 + c^2 + d^2) :: rat;
         n0 = of_int (N $$ (𝗏-3,i));
         n1 = of_int (N $$ (𝗏-2,i));
         n2 = of_int (N $$ (𝗏-1,i))
     in
       - n0 * of_nat c / D +
         n1 * of_nat d / D +
         n2 * of_nat a / D)"
  unfolding brc_terminal_coeff_def
  by simp

lemma brc_terminal_coeff_3:
  "brc_terminal_coeff a b c d i 3 =
    (let D =
       of_nat (a^2 + b^2 + c^2 + d^2) :: rat;
         n0 = of_int (N $$ (𝗏-3,i));
         n1 = of_int (N $$ (𝗏-2,i));
         n2 = of_int (N $$ (𝗏-1,i))
     in
       - n0 * of_nat d / D -
         n1 * of_nat c / D +
         n2 * of_nat b / D)"
  unfolding brc_terminal_coeff_def
  by simp

lemma brc_terminal_inverse_row0:
  fixes a b c d i :: nat
  fixes y0 y1 y2 y3 :: rat
  shows
    "of_int (N $$ (𝗏-3,i)) *
       one_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))
     =
       (of_int (N $$ (𝗏-3,i)) * of_nat a /
        of_nat (a^2+b^2+c^2+d^2)) * y0 -
       (of_int (N $$ (𝗏-3,i)) * of_nat b /
        of_nat (a^2+b^2+c^2+d^2)) * y1 -
       (of_int (N $$ (𝗏-3,i)) * of_nat c /
        of_nat (a^2+b^2+c^2+d^2)) * y2 -
       (of_int (N $$ (𝗏-3,i)) * of_nat d /
        of_nat (a^2+b^2+c^2+d^2)) * y3"
  by (simp only:
      y_inv_of.simps
      y_inv_reversible.simps
      snd_conv
      one_of.simps
      divide_inverse
      diff_conv_add_uminus
      distrib_left distrib_right
      minus_mult_left minus_mult_right
      mult.assoc mult.commute mult.left_commute
      add.assoc add.commute add.left_commute)

lemma brc_terminal_inverse_row1:
  fixes a b c d i :: nat
  fixes y0 y1 y2 y3 :: rat
  shows
    "of_int (N $$ (𝗏-2,i)) *
       two_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))
     =
       (of_int (N $$ (𝗏-2,i)) * of_nat b /
        of_nat (a^2+b^2+c^2+d^2)) * y0 +
       (of_int (N $$ (𝗏-2,i)) * of_nat a /
        of_nat (a^2+b^2+c^2+d^2)) * y1 +
       (of_int (N $$ (𝗏-2,i)) * of_nat d /
        of_nat (a^2+b^2+c^2+d^2)) * y2 -
       (of_int (N $$ (𝗏-2,i)) * of_nat c /
        of_nat (a^2+b^2+c^2+d^2)) * y3"
  by (simp only:
      y_inv_of.simps
      y_inv_reversible.simps
      prod.sel(2)
      two_of.simps
      divide_inverse
      diff_conv_add_uminus
      distrib_left distrib_right
      minus_mult_left minus_mult_right
      mult.assoc mult.commute mult.left_commute
      add.assoc add.commute add.left_commute)

lemma brc_terminal_inverse_row2:
  fixes a b c d i :: nat
  fixes y0 y1 y2 y3 :: rat
  shows
    "of_int (N $$ (𝗏-1,i)) *
       three_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))
     =
       (of_int (N $$ (𝗏-1,i)) * of_nat c /
        of_nat (a^2+b^2+c^2+d^2)) * y0 -
       (of_int (N $$ (𝗏-1,i)) * of_nat d /
        of_nat (a^2+b^2+c^2+d^2)) * y1 +
       (of_int (N $$ (𝗏-1,i)) * of_nat a /
        of_nat (a^2+b^2+c^2+d^2)) * y2 +
       (of_int (N $$ (𝗏-1,i)) * of_nat b /
        of_nat (a^2+b^2+c^2+d^2)) * y3"
proof -
  let ?D =
    "of_nat (a^2+b^2+c^2+d^2) :: rat"

  have inv:
    "three_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))
     =
     (of_nat c*y0 +
      of_nat a*y2 +
      of_nat b*y3 -
      of_nat d*y1) / ?D"
    by simp

  have reordered:
    "three_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))
     =
     (of_nat c*y0 -
      of_nat d*y1 +
      of_nat a*y2 +
      of_nat b*y3) / ?D"
    using inv
    by (simp add: algebra_simps)

  show ?thesis
    using reordered
    by (simp add:
        algebra_simps
        add_divide_distrib
        diff_divide_distrib)
qed

lemma brc_terminal_last_three_affine:
  fixes a b c d i :: nat
  fixes y0 y1 y2 y3 :: rat
  shows
    "of_int (N $$ (𝗏-3,i)) *
       one_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3))) +
     of_int (N $$ (𝗏-2,i)) *
       two_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3))) +
     of_int (N $$ (𝗏-1,i)) *
       three_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))
     =
     brc_terminal_coeff a b c d i 0 * y0 +
     brc_terminal_coeff a b c d i 1 * y1 +
     brc_terminal_coeff a b c d i 2 * y2 +
     brc_terminal_coeff a b c d i 3 * y3"
proof -
  let ?D =
    "of_nat (a^2+b^2+c^2+d^2) :: rat"

  let ?n0 =
    "of_int (N $$ (𝗏-3,i)) :: rat"

  let ?n1 =
    "of_int (N $$ (𝗏-2,i)) :: rat"

  let ?n2 =
    "of_int (N $$ (𝗏-1,i)) :: rat"

  have row0:
    "?n0 *
       one_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))
     =
       (?n0 * of_nat a / ?D) * y0 -
       (?n0 * of_nat b / ?D) * y1 -
       (?n0 * of_nat c / ?D) * y2 -
       (?n0 * of_nat d / ?D) * y3"
    using brc_terminal_inverse_row0[
      where a=a and b=b and c=c and d=d and i=i]
    .

  have row1:
    "?n1 *
       two_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))
     =
       (?n1 * of_nat b / ?D) * y0 +
       (?n1 * of_nat a / ?D) * y1 +
       (?n1 * of_nat d / ?D) * y2 -
       (?n1 * of_nat c / ?D) * y3"
    using brc_terminal_inverse_row1[
      where a=a and b=b and c=c and d=d and i=i]
    .

  have row2:
    "?n2 *
       three_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))
     =
       (?n2 * of_nat c / ?D) * y0 -
       (?n2 * of_nat d / ?D) * y1 +
       (?n2 * of_nat a / ?D) * y2 +
       (?n2 * of_nat b / ?D) * y3"
    using brc_terminal_inverse_row2[
      where a=a and b=b and c=c and d=d and i=i]
    .

  have rows:
    "?n0 *
       one_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3))) +
     ?n1 *
       two_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3))) +
     ?n2 *
       three_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))
     =
       ((?n0 * of_nat a / ?D) * y0 -
        (?n0 * of_nat b / ?D) * y1 -
        (?n0 * of_nat c / ?D) * y2 -
        (?n0 * of_nat d / ?D) * y3) +
       ((?n1 * of_nat b / ?D) * y0 +
        (?n1 * of_nat a / ?D) * y1 +
        (?n1 * of_nat d / ?D) * y2 -
        (?n1 * of_nat c / ?D) * y3) +
       ((?n2 * of_nat c / ?D) * y0 -
        (?n2 * of_nat d / ?D) * y1 +
        (?n2 * of_nat a / ?D) * y2 +
        (?n2 * of_nat b / ?D) * y3)"
    using row0 row1 row2
    by argo

  have group0:
    "brc_terminal_coeff a b c d i 0 * y0
     =
       (?n0 * of_nat a / ?D) * y0 +
       (?n1 * of_nat b / ?D) * y0 +
       (?n2 * of_nat c / ?D) * y0"
    by (simp only:
        brc_terminal_coeff_0
        Let_def
        distrib_right)

  have group1:
    "brc_terminal_coeff a b c d i 1 * y1
     =
       - (?n0 * of_nat b / ?D) * y1 +
       (?n1 * of_nat a / ?D) * y1 -
       (?n2 * of_nat d / ?D) * y1"
    by (simp only:
        brc_terminal_coeff_1
        Let_def
        diff_conv_add_uminus
        distrib_right
        minus_mult_left
        mult.assoc
        add.assoc)

  have group2:
    "brc_terminal_coeff a b c d i 2 * y2
     =
       - (?n0 * of_nat c / ?D) * y2 +
       (?n1 * of_nat d / ?D) * y2 +
       (?n2 * of_nat a / ?D) * y2"
    by (simp only:
        brc_terminal_coeff_2
        Let_def
        diff_conv_add_uminus
        distrib_right
        minus_mult_left
        mult.assoc
        add.assoc)

  have group3:
    "brc_terminal_coeff a b c d i 3 * y3
     =
       - (?n0 * of_nat d / ?D) * y3 -
       (?n1 * of_nat c / ?D) * y3 +
       (?n2 * of_nat b / ?D) * y3"
    by (simp only:
        brc_terminal_coeff_3
        Let_def
        diff_conv_add_uminus
        distrib_right
        minus_mult_left
        mult.assoc
        add.assoc)

  show ?thesis
    apply (rule trans[OF rows])
    apply (simp only:
        group0 group1 group2 group3
        diff_conv_add_uminus
        minus_mult_left
        add.assoc add.commute add.left_commute)
    done
qed

lemma brc_terminal_L_affine:
  fixes a b c d i :: nat
  fixes x x' :: "rat mat"
  fixes xv1 y0 y1 y2 y3 :: rat
  assumes v_ge3:
    "3 ≤ 𝗏"
  assumes nzsum:
    "a^2 + b^2 + c^2 + d^2 ≠ 0"
  assumes preserve:
    "∀h. h < 𝗏 - 3 ⟶ h < 𝗏 ⟶
       x' $$ (h,0) = x $$ (h,0)"
  assumes tuple:
    "y_of
       ((a,b,c,d),
        (brc_extend_x x' xv1 $$ (𝗏-3,0),
         brc_extend_x x' xv1 $$ (𝗏-2,0),
         brc_extend_x x' xv1 $$ (𝗏-1,0),
         brc_extend_x x' xv1 $$ (𝗏,0)))
     =
     (y0,y1,y2,y3)"
  shows
    "brc_L x' i =
       brc_terminal_coeff a b c d i 0 * y0 +
       brc_terminal_coeff a b c d i 1 * y1 +
       brc_terminal_coeff a b c d i 2 * y2 +
       brc_terminal_coeff a b c d i 3 * y3 +
       brc_terminal_tail x i"
proof -
  have index0:
    "𝗏 - 3 < 𝗏"
    using v_ge3
    by (cases 𝗏) auto

  have index1:
    "𝗏 - 2 < 𝗏"
    using v_ge3
    by (cases 𝗏) auto

  have index2:
    "𝗏 - 1 < 𝗏"
    using v_ge3
    by (cases 𝗏) auto

  have old0:
    "brc_extend_x x' xv1 $$ (𝗏-3,0) =
     x' $$ (𝗏-3,0)"
    using index0
    by (rule brc_extend_x_old)

  have old1:
    "brc_extend_x x' xv1 $$ (𝗏-2,0) =
     x' $$ (𝗏-2,0)"
    using index1
    by (rule brc_extend_x_old)

  have old2:
    "brc_extend_x x' xv1 $$ (𝗏-1,0) =
     x' $$ (𝗏-1,0)"
    using index2
    by (rule brc_extend_x_old)

  have inverse:
    "brc_extend_x x' xv1 $$ (𝗏-3,0) =
       one_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3))) ∧
     brc_extend_x x' xv1 $$ (𝗏-2,0) =
       two_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3))) ∧
     brc_extend_x x' xv1 $$ (𝗏-1,0) =
       three_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3))) ∧
     brc_extend_x x' xv1 $$ (𝗏,0) =
       four_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
    using brc_terminal_tuple_inverse_entries[
      OF nzsum tuple]
    .

  have entry0:
    "x' $$ (𝗏-3,0) =
       one_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
    using inverse old0
    by simp

  have entry1:
    "x' $$ (𝗏-2,0) =
       two_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
    using inverse old1
    by simp

  have entry2:
    "x' $$ (𝗏-1,0) =
       three_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
    using inverse old2
    by simp

  have split:
    "brc_L x' i =
       brc_terminal_tail x' i +
       of_int (N $$ (𝗏-3,i)) * x' $$ (𝗏-3,0) +
       of_int (N $$ (𝗏-2,i)) * x' $$ (𝗏-2,0) +
       of_int (N $$ (𝗏-1,i)) * x' $$ (𝗏-1,0)"
    using brc_terminal_form_split_last_three[
      OF v_ge3, of x' i]
    unfolding brc_terminal_tail_def
    .

  have tail:
    "brc_terminal_tail x' i =
     brc_terminal_tail x i"
    using brc_terminal_tail_preserve[
      OF preserve, of i]
    .

  have affine:
    "of_int (N $$ (𝗏-3,i)) *
       one_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3))) +
     of_int (N $$ (𝗏-2,i)) *
       two_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3))) +
     of_int (N $$ (𝗏-1,i)) *
       three_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))
     =
       brc_terminal_coeff a b c d i 0 * y0 +
       brc_terminal_coeff a b c d i 1 * y1 +
       brc_terminal_coeff a b c d i 2 * y2 +
       brc_terminal_coeff a b c d i 3 * y3"
    using brc_terminal_last_three_affine[
      where a=a and b=b and c=c and d=d and i=i]
    .

  have terminal_three:
    "of_int (N $$ (𝗏-3,i)) * x' $$ (𝗏-3,0) +
     of_int (N $$ (𝗏-2,i)) * x' $$ (𝗏-2,0) +
     of_int (N $$ (𝗏-1,i)) * x' $$ (𝗏-1,0)
     =
     brc_terminal_coeff a b c d i 0 * y0 +
     brc_terminal_coeff a b c d i 1 * y1 +
     brc_terminal_coeff a b c d i 2 * y2 +
     brc_terminal_coeff a b c d i 3 * y3"
    by (simp only:
        entry0 entry1 entry2
        affine)

  have split_grouped:
    "brc_L x' i =
       brc_terminal_tail x' i +
       (of_int (N $$ (𝗏-3,i)) * x' $$ (𝗏-3,0) +
        of_int (N $$ (𝗏-2,i)) * x' $$ (𝗏-2,0) +
        of_int (N $$ (𝗏-1,i)) * x' $$ (𝗏-1,0))"
    using split
    by (simp only: add.assoc)

  have assembled:
    "brc_terminal_tail x' i +
       (of_int (N $$ (𝗏-3,i)) * x' $$ (𝗏-3,0) +
        of_int (N $$ (𝗏-2,i)) * x' $$ (𝗏-2,0) +
        of_int (N $$ (𝗏-1,i)) * x' $$ (𝗏-1,0))
     =
     brc_terminal_tail x i +
       (brc_terminal_coeff a b c d i 0 * y0 +
        brc_terminal_coeff a b c d i 1 * y1 +
        brc_terminal_coeff a b c d i 2 * y2 +
        brc_terminal_coeff a b c d i 3 * y3)"
    apply (subst tail)
    apply (subst terminal_three)
    apply (rule refl)
    done

  have combined:
    "brc_L x' i =
     brc_terminal_tail x i +
       (brc_terminal_coeff a b c d i 0 * y0 +
        brc_terminal_coeff a b c d i 1 * y1 +
        brc_terminal_coeff a b c d i 2 * y2 +
        brc_terminal_coeff a b c d i 3 * y3)"
    using split_grouped assembled
    by argo

  show ?thesis
    apply (subst combined)
    apply (simp only:
        add.assoc add.commute add.left_commute)
    done
qed

lemma brc_terminal_choose_y:
  fixes a b c d :: nat
  fixes x :: "rat mat"
  shows
    "∃y0 y1 y2 :: rat.
       (brc_terminal_coeff a b c d (𝗏-3) 0 * y0 +
        brc_terminal_coeff a b c d (𝗏-3) 1 * y1 +
        brc_terminal_coeff a b c d (𝗏-3) 2 * y2 +
        (brc_terminal_coeff a b c d (𝗏-3) 3 +
         brc_terminal_tail x (𝗏-3)))^2 +
       (brc_terminal_coeff a b c d (𝗏-2) 0 * y0 +
        brc_terminal_coeff a b c d (𝗏-2) 1 * y1 +
        brc_terminal_coeff a b c d (𝗏-2) 2 * y2 +
        (brc_terminal_coeff a b c d (𝗏-2) 3 +
         brc_terminal_tail x (𝗏-2)))^2 +
       (brc_terminal_coeff a b c d (𝗏-1) 0 * y0 +
        brc_terminal_coeff a b c d (𝗏-1) 1 * y1 +
        brc_terminal_coeff a b c d (𝗏-1) 2 * y2 +
        (brc_terminal_coeff a b c d (𝗏-1) 3 +
         brc_terminal_tail x (𝗏-1)))^2
       =
       y0^2 + y1^2 + y2^2"
proof -
  show ?thesis
    by (rule brc_three_linear_squares)
qed

lemma brc_terminal_step_exists:
  fixes a b c d w :: nat
  fixes x :: "rat mat"
  assumes v_form:
    "𝗏 = 4 * w - 1"
  assumes w_pos:
    "0 < w"
  assumes nzsum:
    "a^2 + b^2 + c^2 + d^2 ≠ 0"
  shows
    "∃x' xv1 y0 y1 y2.
       (∀h. h < 𝗏 - 3 ⟶ h < 𝗏 ⟶
          x' $$ (h,0) = x $$ (h,0)) ∧
       y_of
        ((a,b,c,d),
         (brc_extend_x x' xv1 $$ (𝗏-3,0),
          brc_extend_x x' xv1 $$ (𝗏-2,0),
          brc_extend_x x' xv1 $$ (𝗏-1,0),
          brc_extend_x x' xv1 $$ (𝗏,0)))
       =
       (y0,y1,y2,1) ∧
       brc_L x' (𝗏-3)^2 +
       brc_L x' (𝗏-2)^2 +
       brc_L x' (𝗏-1)^2
       =
       y0^2 + y1^2 + y2^2"
proof -
  have v_ge3:
    "3 ≤ 𝗏"
    using v_form w_pos
    by (cases w) auto

  obtain y0 y1 y2 :: rat where match:
    "(brc_terminal_coeff a b c d (𝗏-3) 0 * y0 +
      brc_terminal_coeff a b c d (𝗏-3) 1 * y1 +
      brc_terminal_coeff a b c d (𝗏-3) 2 * y2 +
      (brc_terminal_coeff a b c d (𝗏-3) 3 +
       brc_terminal_tail x (𝗏-3)))^2 +
     (brc_terminal_coeff a b c d (𝗏-2) 0 * y0 +
      brc_terminal_coeff a b c d (𝗏-2) 1 * y1 +
      brc_terminal_coeff a b c d (𝗏-2) 2 * y2 +
      (brc_terminal_coeff a b c d (𝗏-2) 3 +
       brc_terminal_tail x (𝗏-2)))^2 +
     (brc_terminal_coeff a b c d (𝗏-1) 0 * y0 +
      brc_terminal_coeff a b c d (𝗏-1) 1 * y1 +
      brc_terminal_coeff a b c d (𝗏-1) 2 * y2 +
      (brc_terminal_coeff a b c d (𝗏-1) 3 +
       brc_terminal_tail x (𝗏-1)))^2
     =
     y0^2 + y1^2 + y2^2"
    using brc_terminal_choose_y[
      where a=a and b=b and c=c and d=d and x=x]
    by blast

  have update:
    "∃x' xv1.
       (∀h. h < 𝗏 - 3 ⟶ h < 𝗏 ⟶
          x' $$ (h,0) = x $$ (h,0)) ∧
       y_of
        ((a,b,c,d),
         (brc_extend_x x' xv1 $$ (𝗏-3,0),
          brc_extend_x x' xv1 $$ (𝗏-2,0),
          brc_extend_x x' xv1 $$ (𝗏-1,0),
          brc_extend_x x' xv1 $$ (𝗏,0)))
       =
       (y0,y1,y2,1)"
    using brc_terminal_update_from_y[
      OF v_form w_pos nzsum]
    by blast

  obtain x' xv1 where preserve:
    "∀h. h < 𝗏 - 3 ⟶ h < 𝗏 ⟶
       x' $$ (h,0) = x $$ (h,0)"
    and tuple:
    "y_of
       ((a,b,c,d),
        (brc_extend_x x' xv1 $$ (𝗏-3,0),
         brc_extend_x x' xv1 $$ (𝗏-2,0),
         brc_extend_x x' xv1 $$ (𝗏-1,0),
         brc_extend_x x' xv1 $$ (𝗏,0)))
     =
     (y0,y1,y2,1)"
    using update
    by blast

  have L0:
    "brc_L x' (𝗏-3) =
       brc_terminal_coeff a b c d (𝗏-3) 0 * y0 +
       brc_terminal_coeff a b c d (𝗏-3) 1 * y1 +
       brc_terminal_coeff a b c d (𝗏-3) 2 * y2 +
       (brc_terminal_coeff a b c d (𝗏-3) 3 +
        brc_terminal_tail x (𝗏-3))"
    using brc_terminal_L_affine[
      OF v_ge3 nzsum preserve tuple]
    by (simp only: mult_1 add.assoc)

  have L1:
    "brc_L x' (𝗏-2) =
       brc_terminal_coeff a b c d (𝗏-2) 0 * y0 +
       brc_terminal_coeff a b c d (𝗏-2) 1 * y1 +
       brc_terminal_coeff a b c d (𝗏-2) 2 * y2 +
       (brc_terminal_coeff a b c d (𝗏-2) 3 +
        brc_terminal_tail x (𝗏-2))"
    using brc_terminal_L_affine[
      OF v_ge3 nzsum preserve tuple]
    by (simp only: mult_1 add.assoc)

  have L2:
    "brc_L x' (𝗏-1) =
       brc_terminal_coeff a b c d (𝗏-1) 0 * y0 +
       brc_terminal_coeff a b c d (𝗏-1) 1 * y1 +
       brc_terminal_coeff a b c d (𝗏-1) 2 * y2 +
       (brc_terminal_coeff a b c d (𝗏-1) 3 +
        brc_terminal_tail x (𝗏-1))"
    using brc_terminal_L_affine[
      OF v_ge3 nzsum preserve tuple]
    by (simp only: mult_1 add.assoc)

  have terminal_identity:
    "brc_L x' (𝗏-3)^2 +
     brc_L x' (𝗏-2)^2 +
     brc_L x' (𝗏-1)^2
     =
     y0^2 + y1^2 + y2^2"
    using L0 L1 L2 match
    by metis

  show ?thesis
    using preserve tuple terminal_identity
    by blast
qed

lemma brc_minus_prefix_preserve_terminal:
  fixes a b c d w :: nat
  fixes x x' :: "rat mat"
  fixes xv1 :: rat
  assumes v_form:
    "𝗏 = 4 * w - 1"
  assumes w_pos:
    "0 < w"
  assumes prefix:
    "brc_minus_prefix_eliminated
       a b c d x xv1 (w - 1)"
  assumes preserve:
    "∀h. h < 𝗏 - 3 ⟶ h < 𝗏 ⟶
       x' $$ (h,0) = x $$ (h,0)"
  shows
    "brc_minus_prefix_eliminated
       a b c d x' xv1 (w - 1)"
proof -
  show ?thesis
    unfolding brc_minus_prefix_eliminated_def
  proof (intro allI impI)
    fix t
    assume t_lt:
      "t < w - 1"

    have block_bound:
      "4 * Suc t ≤ 𝗏 - 3"
    proof -
      have suc_bound:
        "Suc t ≤ w - 1"
        using t_lt
        by simp

      have mult_bound:
        "4 * Suc t ≤ 4 * (w - 1)"
        using suc_bound
        by simp

      have terminal_index:
        "4 * (w - 1) = 𝗏 - 3"
        using v_form w_pos
        by simp

      show ?thesis
        using mult_bound terminal_index
        by simp
    qed

    have entry_eq:
      "brc_extend_x x' xv1 $$ (i,0) =
       brc_extend_x x xv1 $$ (i,0)"
      if i_lt:
        "i < 4 * Suc t"
      for i :: nat
    proof -
      have i_lt_terminal:
        "i < 𝗏 - 3"
        using i_lt block_bound
        by simp

      have i_lt_v:
        "i < 𝗏"
        using i_lt_terminal
        by simp

      have xx:
        "x' $$ (i,0) = x $$ (i,0)"
        using preserve i_lt_terminal i_lt_v
        by blast

      show ?thesis
        using xx i_lt_v
        unfolding brc_extend_x_def
        by simp
    qed

    have old:
      "y_block_sqsum a b c d
         (brc_extend_x x xv1) t
       =
       (∑j∈{0..<4}.
         (∑r∈{0..<4 * Suc t}.
           of_int
             (N $$ (4 * Suc t-r-1,
                     4 * Suc t-j-1)) *
           brc_extend_x x xv1 $$
             (4 * Suc t-r-1,0))^2)"
      using prefix t_lt
      unfolding brc_minus_prefix_eliminated_def
      by blast

    have block_eq:
      "y_block_sqsum a b c d
         (brc_extend_x x' xv1) t
       =
       y_block_sqsum a b c d
         (brc_extend_x x xv1) t"
    proof -
      show ?thesis
        unfolding y_block_sqsum_def
        using entry_eq
        by simp
    qed

    have rhs_eq:
      "(∑j∈{0..<4}.
         (∑r∈{0..<4 * Suc t}.
           of_int
             (N $$ (4 * Suc t-r-1,
                     4 * Suc t-j-1)) *
           brc_extend_x x' xv1 $$
             (4 * Suc t-r-1,0))^2)
       =
       (∑j∈{0..<4}.
         (∑r∈{0..<4 * Suc t}.
           of_int
             (N $$ (4 * Suc t-r-1,
                     4 * Suc t-j-1)) *
           brc_extend_x x xv1 $$
             (4 * Suc t-r-1,0))^2)"
    proof -
      have entry:
        "brc_extend_x x' xv1 $$
           (4 * Suc t-r-1,0)
         =
         brc_extend_x x xv1 $$
           (4 * Suc t-r-1,0)"
        if r_mem:
          "r ∈ {0..<4 * Suc t}"
        for r :: nat
      proof -
        have index_lt:
          "4 * Suc t-r-1 < 4 * Suc t"
          using r_mem
          by simp

        show ?thesis
          using entry_eq[OF index_lt] .
      qed

      show ?thesis
        using entry
        by (intro sum.cong) auto
    qed

    have result:
      "y_block_sqsum a b c d
         (brc_extend_x x' xv1) t
       =
       (∑j∈{0..<4}.
         (∑r∈{0..<4 * Suc t}.
           of_int
             (N $$ (4 * Suc t-r-1,
                     4 * Suc t-j-1)) *
           brc_extend_x x' xv1 $$
             (4 * Suc t-r-1,0))^2)"
      using block_eq old rhs_eq
      by simp

    show
      "y_block_sqsum a b c d
         (brc_extend_x x' xv1) t
       =
       (∑j∈{0..<4}.
         (∑r∈{0..<4 * Suc t}.
           of_int
             (N $$ (4 * Suc t-r-1,
                     4 * Suc t-j-1)) *
           brc_extend_x x' xv1 $$
             (4 * Suc t-r-1,0))^2)"
      using result .
  qed
qed

lemma brc_minus_full_elimination_exists:
  fixes a b c d w :: nat
  assumes v_form:
    "𝗏 = 4 * w - 1"
  assumes w_pos:
    "0 < w"
  assumes four_sq:
    "a^2 + b^2 + c^2 + d^2 = 𝗄 - Λ"
  assumes nzsum:
    "a^2 + b^2 + c^2 + d^2 ≠ 0"
  shows
    "∃x xv1 y0 y1 y2.
       brc_minus_prefix_eliminated
         a b c d x xv1 (w - 1) ∧
       y_of
        ((a,b,c,d),
         (brc_extend_x x xv1 $$ (𝗏-3,0),
          brc_extend_x x xv1 $$ (𝗏-2,0),
          brc_extend_x x xv1 $$ (𝗏-1,0),
          brc_extend_x x xv1 $$ (𝗏,0)))
       =
       (y0,y1,y2,1) ∧
       brc_L x (𝗏-3)^2 +
       brc_L x (𝗏-2)^2 +
       brc_L x (𝗏-1)^2
       =
       y0^2 + y1^2 + y2^2"
proof -
  obtain x0 :: "rat mat" where interior:
    "∀xv1 :: rat.
       brc_minus_prefix_eliminated
         a b c d x0 xv1 (w - 1)"
    using brc_minus_interior_prefix_exists_all_xv1[
      OF v_form w_pos four_sq nzsum]
    by blast

  obtain x xv1 y0 y1 y2 where preserve:
    "∀h. h < 𝗏 - 3 ⟶ h < 𝗏 ⟶
       x $$ (h,0) = x0 $$ (h,0)"
    and tuple:
    "y_of
      ((a,b,c,d),
       (brc_extend_x x xv1 $$ (𝗏-3,0),
        brc_extend_x x xv1 $$ (𝗏-2,0),
        brc_extend_x x xv1 $$ (𝗏-1,0),
        brc_extend_x x xv1 $$ (𝗏,0)))
     =
     (y0,y1,y2,1)"
    and terminal:
    "brc_L x (𝗏-3)^2 +
     brc_L x (𝗏-2)^2 +
     brc_L x (𝗏-1)^2
     =
     y0^2 + y1^2 + y2^2"
    using brc_terminal_step_exists[
      OF v_form w_pos nzsum,
      of x0]
    by blast

  have old_prefix:
    "brc_minus_prefix_eliminated
       a b c d x0 xv1 (w - 1)"
    using interior
    by blast

  have new_prefix:
    "brc_minus_prefix_eliminated
       a b c d x xv1 (w - 1)"
    using brc_minus_prefix_preserve_terminal[
      OF v_form w_pos old_prefix preserve]
    .

  show ?thesis
    using new_prefix tuple terminal
    by blast
qed

lemma sum_upt_reverse:
  fixes f :: "nat ⇒ rat"
  shows
    "(∑r∈{0..<m}. f (m-r-1))
     =
     (∑r∈{0..<m}. f r)"
proof -
  let ?p = "λr::nat. m-r-1"

  have maps:
    "?p ` {0..<m} = {0..<m}"
  proof
    show "?p ` {0..<m} ⊆ {0..<m}"
      by auto
  next
    show "{0..<m} ⊆ ?p ` {0..<m}"
    proof
      fix r
      assume r_mem:
        "r ∈ {0..<m}"

      have image_mem:
        "m-r-1 ∈ {0..<m}"
        using r_mem
        by simp

      have inverse:
        "m-(m-r-1)-1 = r"
        using r_mem
        by simp

      show "r ∈ ?p ` {0..<m}"
        using image_mem inverse
        by force
    qed
  qed

  have inj:
    "inj_on ?p {0..<m}"
  proof
    fix r s
    assume r_mem:
      "r ∈ {0..<m}"
    assume s_mem:
      "s ∈ {0..<m}"
    assume eq:
      "m-r-1 = m-s-1"

    show "r = s"
      using r_mem s_mem eq
      by simp
  qed

  have reindex:
    "(∑r∈{0..<m}. f (?p r))
     =
     (∑r∈?p ` {0..<m}. f r)"
    using inj
    by (simp add: sum.reindex)

  show ?thesis
    using reindex maps
    by simp
qed

lemma brc_L_eq_prefix_if_tail_zero:
  fixes x :: "rat mat"
  fixes m i :: nat
  assumes m_bound:
    "m ≤ 𝗏"
  assumes tail_zero:
    "(∑r∈{m..<𝗏}.
       of_int (N $$ (r,i)) * x $$ (r,0)) = 0"
  shows
    "brc_L x i =
     (∑r∈{0..<m}.
       of_int (N $$ (r,i)) * x $$ (r,0))"
proof -
  have split:
    "(∑r∈{0..<𝗏}.
       of_int (N $$ (r,i)) * x $$ (r,0))
     =
     (∑r∈{0..<m}.
       of_int (N $$ (r,i)) * x $$ (r,0))
     +
     (∑r∈{m..<𝗏}.
       of_int (N $$ (r,i)) * x $$ (r,0))"
    using m_bound
    by (simp add: sum.atLeastLessThan_concat)

  show ?thesis
    unfolding brc_L_def
    using split tail_zero
    by simp
qed

lemma brc_reversed_prefix_eq_L:
  fixes x :: "rat mat"
  fixes m i :: nat
  assumes m_bound:
    "m ≤ 𝗏"
  assumes tail_zero:
    "(∑r∈{m..<𝗏}.
       of_int (N $$ (r,i)) * x $$ (r,0)) = 0"
  shows
    "(∑r∈{0..<m}.
       of_int (N $$ (m-r-1,i)) *
       x $$ (m-r-1,0))
     =
     brc_L x i"
proof -
  have reverse:
    "(∑r∈{0..<m}.
       of_int (N $$ (m-r-1,i)) *
       x $$ (m-r-1,0))
     =
     (∑r∈{0..<m}.
       of_int (N $$ (r,i)) *
       x $$ (r,0))"
    using sum_upt_reverse[
      of "λr.
        of_int (N $$ (r,i)) *
        x $$ (r,0)" m]
    by simp

  have prefix:
    "brc_L x i =
     (∑r∈{0..<m}.
       of_int (N $$ (r,i)) *
       x $$ (r,0))"
    using brc_L_eq_prefix_if_tail_zero[
      OF m_bound tail_zero]
    .

  show ?thesis
    using reverse prefix
    by simp
qed

lemma brc_minus_good_block_eq_L:
  fixes a b c d q h :: nat
  fixes x :: "rat mat"
  fixes xv1 :: rat
  assumes good:
    "brc_minus_prefix_good
       a b c d x xv1 q"
  assumes h_lt:
    "h < q"
  assumes q_bound:
    "4 * q ≤ 𝗏"
  shows
    "y_block_sqsum a b c d
       (brc_extend_x x xv1) h
     =
     (∑j∈{0..<4}.
        (brc_L x (4*h+j))^2)"
proof -
  have prefix:
    "brc_minus_prefix_eliminated
       a b c d x xv1 q"
    using good
    unfolding brc_minus_prefix_good_def
    by blast

  have eliminated:
    "y_block_sqsum a b c d
       (brc_extend_x x xv1) h
     =
     (∑j∈{0..<4}.
       (∑r∈{0..<4 * Suc h}.
          of_int
            (N $$ (4 * Suc h-r-1,
                    4 * Suc h-j-1)) *
          brc_extend_x x xv1 $$
            (4 * Suc h-r-1,0))^2)"
    using prefix h_lt
    unfolding brc_minus_prefix_eliminated_def
    by blast

  have block_bound:
    "4 * Suc h ≤ 𝗏"
  proof -
    have "Suc h ≤ q"
      using h_lt
      by simp
    then have "4 * Suc h ≤ 4 * q"
      by simp
    then show ?thesis
      using q_bound
      by simp
  qed

  have form:
    "(∑r∈{0..<4 * Suc h}.
       of_int
         (N $$ (4 * Suc h-r-1,
                 4 * Suc h-j-1)) *
       brc_extend_x x xv1 $$
         (4 * Suc h-r-1,0))
     =
     brc_L x (4 * Suc h-j-1)"
    if j_mem:
      "j ∈ {0..<4}"
    for j :: nat
  proof -
    have j_lt:
      "j < 4"
      using j_mem
      by simp

    let ?k = "4-j-1"

    have k_lt:
      "?k < 4"
      using j_lt
      by simp

    have tail_raw:
      "(∑r∈{4 * Suc h..<𝗏}.
         of_int (N $$ (r,4*h+?k)) *
         x $$ (r,0)) = 0"
      using good h_lt k_lt
      unfolding brc_minus_prefix_good_def
      by blast

    have column_eq:
      "4*h + ?k = 4 * Suc h-j-1"
      using j_lt
      by simp

    have tail:
      "(∑r∈{4 * Suc h..<𝗏}.
         of_int
           (N $$ (r,4 * Suc h-j-1)) *
         x $$ (r,0)) = 0"
      using tail_raw column_eq
      by simp

    have reversed:
      "(∑r∈{0..<4 * Suc h}.
         of_int
           (N $$ (4 * Suc h-r-1,
                   4 * Suc h-j-1)) *
         x $$ (4 * Suc h-r-1,0))
       =
       brc_L x (4 * Suc h-j-1)"
      using brc_reversed_prefix_eq_L[
        OF block_bound tail]
      .

    have entries:
      "brc_extend_x x xv1 $$
         (4 * Suc h-r-1,0)
       =
       x $$ (4 * Suc h-r-1,0)"
      if r_mem:
        "r ∈ {0..<4 * Suc h}"
      for r :: nat
    proof -
      have index_lt:
        "4 * Suc h-r-1 < 4 * Suc h"
        using r_mem
        by simp

      have index_v:
        "4 * Suc h-r-1 < 𝗏"
        using index_lt block_bound
        by simp

      show ?thesis
        using brc_extend_x_old[OF index_v, of x xv1] .
    qed

    have extended:
      "(∑r∈{0..<4 * Suc h}.
         of_int
           (N $$ (4 * Suc h-r-1,
                   4 * Suc h-j-1)) *
         brc_extend_x x xv1 $$
           (4 * Suc h-r-1,0))
       =
       (∑r∈{0..<4 * Suc h}.
         of_int
           (N $$ (4 * Suc h-r-1,
                   4 * Suc h-j-1)) *
         x $$ (4 * Suc h-r-1,0))"
      using entries
      by (intro sum.cong) auto

    show ?thesis
      using extended reversed
      by simp
  qed

  have reversed_columns:
    "(∑j∈{0..<4}.
       (brc_L x (4 * Suc h-j-1))^2)
     =
     (∑j∈{0..<4}.
       (brc_L x (4*h+j))^2)"
  proof -
    have reverse:
      "(∑j∈{0..<4}.
         (brc_L x (4*h + (4-j-1)))^2)
       =
       (∑j∈{0..<4}.
         (brc_L x (4*h+j))^2)"
      using sum_upt_reverse[
        of "λj. (brc_L x (4*h+j))^2" 4]
      by simp

    have index_eq:
      "4 * Suc h-j-1 = 4*h + (4-j-1)"
      if j_mem:
        "j ∈ {0..<4}"
      for j :: nat
      using j_mem
      by simp

    have left_eq:
      "(∑j∈{0..<4}.
         (brc_L x (4 * Suc h-j-1))^2)
       =
       (∑j∈{0..<4}.
         (brc_L x (4*h + (4-j-1)))^2)"
      using index_eq
      by (intro sum.cong) auto

    show ?thesis
      using left_eq reverse
      by simp
  qed

  have transformed:
    "(∑j∈{0..<4}.
       (∑r∈{0..<4 * Suc h}.
          of_int
            (N $$ (4 * Suc h-r-1,
                    4 * Suc h-j-1)) *
          brc_extend_x x xv1 $$
            (4 * Suc h-r-1,0))^2)
     =
     (∑j∈{0..<4}.
        (brc_L x (4 * Suc h-j-1))^2)"
    using form
    by (intro sum.cong) auto

  show ?thesis
    using eliminated transformed reversed_columns
    by simp
qed

lemma brc_minus_good_prefix_sum_L:
  fixes a b c d q :: nat
  fixes x :: "rat mat"
  fixes xv1 :: rat
  assumes good:
    "brc_minus_prefix_good
       a b c d x xv1 q"
  assumes q_bound:
    "4 * q ≤ 𝗏"
  shows
    "(∑h∈{0..<q}.
       y_block_sqsum a b c d
         (brc_extend_x x xv1) h)
     =
     (∑i∈{0..<4*q}.
       (brc_L x i)^2)"
proof -
  have each_block:
    "y_block_sqsum a b c d
       (brc_extend_x x xv1) h
     =
     (∑j∈{0..<4}.
        (brc_L x (4*h+j))^2)"
    if h_mem:
      "h ∈ {0..<q}"
    for h :: nat
  proof -
    have h_lt:
      "h < q"
      using h_mem
      by simp

    show ?thesis
      using brc_minus_good_block_eq_L[
        OF good h_lt q_bound]
      .
  qed

  have summed_blocks:
    "(∑h∈{0..<q}.
       y_block_sqsum a b c d
         (brc_extend_x x xv1) h)
     =
     (∑h∈{0..<q}.
       (∑j∈{0..<4}.
          (brc_L x (4*h+j))^2))"
    using each_block
    by (intro sum.cong) auto

  have four_terms:
    "(∑j∈{0..<4}.
       (brc_L x (4*h+j))^2)
     =
     (brc_L x (4*h))^2 +
     (brc_L x (4*h+1))^2 +
     (brc_L x (4*h+2))^2 +
     (brc_L x (4*h+3))^2"
    for h :: nat
    by (simp add: numeral.simps(2,3))

  have partition:
    "(∑i∈{0..<4*q}.
       (brc_L x i)^2)
     =
     (∑h∈{0..<q}.
       (∑j∈{0..<4}.
          (brc_L x (4*h+j))^2))"
  proof -
    have blocks:
      "(∑i∈{0..<4*q}.
         (brc_L x i)^2)
       =
       (∑h∈{0..<q}.
          ((brc_L x (4*h))^2 +
           (brc_L x (4*h+1))^2 +
           (brc_L x (4*h+2))^2 +
           (brc_L x (4*h+3))^2))"
      using sum_four_blocks[
        of "λi. (brc_L x i)^2" q]
      .

    have inner:
      "(∑h∈{0..<q}.
         ((brc_L x (4*h))^2 +
          (brc_L x (4*h+1))^2 +
          (brc_L x (4*h+2))^2 +
          (brc_L x (4*h+3))^2))
       =
       (∑h∈{0..<q}.
          (∑j∈{0..<4}.
             (brc_L x (4*h+j))^2))"
      using four_terms
      by (intro sum.cong) auto

    show ?thesis
      using blocks inner
      by simp
  qed

  show ?thesis
    using summed_blocks partition
    by simp
qed

lemma brc_minus_equation_from_good_witness:
  fixes a b c d w :: nat
  fixes x :: "rat mat"
  fixes xv1 y0 y1 y2 :: rat
  assumes v_form:
    "𝗏 = 4 * w - 1"
  assumes w_pos:
    "0 < w"
  assumes four_sq:
    "a^2 + b^2 + c^2 + d^2 = 𝗄 - Λ"
  assumes good:
    "brc_minus_prefix_good
       a b c d x xv1 (w - 1)"
  assumes tuple:
    "y_of
      ((a,b,c,d),
       (brc_extend_x x xv1 $$ (𝗏-3,0),
        brc_extend_x x xv1 $$ (𝗏-2,0),
        brc_extend_x x xv1 $$ (𝗏-1,0),
        brc_extend_x x xv1 $$ (𝗏,0)))
     =
     (y0,y1,y2,1)"
  assumes terminal:
    "brc_L x (𝗏-3)^2 +
     brc_L x (𝗏-2)^2 +
     brc_L x (𝗏-1)^2
     =
     y0^2 + y1^2 + y2^2"
  shows
    "brc_minus_equation"
proof -
  have v_ge3:
    "3 ≤ 𝗏"
    using v_form w_pos
    by (cases w) auto

  have prefix_bound:
    "4 * (w - 1) ≤ 𝗏"
    using v_form w_pos
    by simp

  have prefix_size:
    "4 * (w - 1) = 𝗏 - 3"
    using v_form w_pos
    by simp

  have prefix_sum:
    "(∑h∈{0..<w-1}.
       y_block_sqsum a b c d
         (brc_extend_x x xv1) h)
     =
     (∑i∈{0..<𝗏-3}.
       (brc_L x i)^2)"
  proof -
    have base:
      "(∑h∈{0..<w-1}.
         y_block_sqsum a b c d
           (brc_extend_x x xv1) h)
       =
       (∑i∈{0..<4*(w-1)}.
         (brc_L x i)^2)"
      using brc_minus_good_prefix_sum_L[
        OF good prefix_bound]
      .

    show ?thesis
      using base prefix_size
      by simp
  qed

  have last_block_indices:
    "4 * (w - 1) = 𝗏 - 3"
    "4 * (w - 1) + 1 = 𝗏 - 2"
    "4 * (w - 1) + 2 = 𝗏 - 1"
    "4 * (w - 1) + 3 = 𝗏"
    using v_form w_pos
    by simp_all

  have last_block:
    "y_block_sqsum a b c d
       (brc_extend_x x xv1) (w - 1)
     =
     y0^2 + y1^2 + y2^2 + 1"
    unfolding y_block_sqsum_def
    using tuple last_block_indices
    by simp

  have w_suc:
    "w = Suc (w - 1)"
    using w_pos
    by simp

  have all_y_blocks:
    "(∑h∈{0..<w}.
       y_block_sqsum a b c d
         (brc_extend_x x xv1) h)
     =
     (∑i∈{0..<𝗏-3}.
       (brc_L x i)^2)
     +
     (y0^2 + y1^2 + y2^2 + 1)"
  proof -
    have split:
      "(∑h∈{0..<w}.
         y_block_sqsum a b c d
           (brc_extend_x x xv1) h)
       =
       (∑h∈{0..<w-1}.
         y_block_sqsum a b c d
           (brc_extend_x x xv1) h)
       +
       y_block_sqsum a b c d
         (brc_extend_x x xv1) (w-1)"
    proof -
      have
        "(∑h∈{0..<w}.
           y_block_sqsum a b c d
             (brc_extend_x x xv1) h)
         =
         (∑h∈{0..<Suc (w-1)}.
           y_block_sqsum a b c d
             (brc_extend_x x xv1) h)"
        using w_suc
        by simp

      also have
        "... =
         (∑h∈{0..<w-1}.
           y_block_sqsum a b c d
             (brc_extend_x x xv1) h)
         +
         y_block_sqsum a b c d
           (brc_extend_x x xv1) (w-1)"
        by simp

      finally show ?thesis .
    qed

    show ?thesis
      using split prefix_sum last_block
      by simp
  qed

  have all_L:
    "(∑i∈{0..<𝗏}.
       (brc_L x i)^2)
     =
     (∑i∈{0..<𝗏-3}.
       (brc_L x i)^2)
     +
     (brc_L x (𝗏-3)^2 +
      brc_L x (𝗏-2)^2 +
      brc_L x (𝗏-1)^2)"
  proof -
    have split:
      "(∑i∈{0..<𝗏}.
         (brc_L x i)^2)
       =
       (∑i∈{0..<𝗏-3}.
         (brc_L x i)^2)
       +
       (∑i∈{𝗏-3..<𝗏}.
         (brc_L x i)^2)"
      using v_ge3
      by (simp add: sum.atLeastLessThan_concat)

    have last_three:
      "(∑i∈{𝗏-3..<𝗏}.
         (brc_L x i)^2)
       =
       brc_L x (𝗏-3)^2 +
       brc_L x (𝗏-2)^2 +
       brc_L x (𝗏-1)^2"
      using sum_last_three[
        OF v_ge3,
        of "λi. (brc_L x i)^2"]
      .

    show ?thesis
      using split last_three
      by simp
  qed

  have all_L_terminal:
    "(∑i∈{0..<𝗏}.
       (brc_L x i)^2)
     =
     (∑i∈{0..<𝗏-3}.
       (brc_L x i)^2)
     +
     (y0^2 + y1^2 + y2^2)"
    using all_L terminal
    by simp

  have blocks_eq_L_plus_one:
    "(∑h∈{0..<w}.
       y_block_sqsum a b c d
         (brc_extend_x x xv1) h)
     =
     (∑i∈{0..<𝗏}.
       (brc_L x i)^2) + 1"
  proof -
    have blocks:
      "(∑h∈{0..<w}.
         y_block_sqsum a b c d
           (brc_extend_x x xv1) h)
       =
       (∑i∈{0..<𝗏-3}.
         (brc_L x i)^2)
       + (y0^2 + y1^2 + y2^2 + 1)"
      using all_y_blocks .

    have linear_forms:
      "(∑i∈{0..<𝗏}.
         (brc_L x i)^2)
       =
       (∑i∈{0..<𝗏-3}.
         (brc_L x i)^2)
       + (y0^2 + y1^2 + y2^2)"
      using all_L_terminal .

    show ?thesis
      using blocks linear_forms
      by (simp add: algebra_simps)
  qed

  have transformed:
    "(∑i∈{0..<𝗏}.
       (brc_L x i)^2)
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
         (∑h∈{0..<w}.
            y_block_sqsum a b c d
              (brc_extend_x x xv1) h)"
      using brc_x_equation_minus_transformed[
        OF v_form w_pos,
        of a b c d x xv1]
        four_sq
      by simp

    show ?thesis
      using base
      unfolding brc_L_def
      by simp
  qed

  have terminal_equation:
    "of_nat (𝗄 - Λ) * xv1^2
     =
     of_nat Λ *
       (∑j∈{0..<𝗏}. x $$ (j,0))^2
     + 1"
    using transformed blocks_eq_L_plus_one
    by linarith

  have terminal_equation_square:
    "of_nat (𝗄 - Λ) * xv1^2
     =
     of_nat Λ *
       (∑j∈{0..<𝗏}. x $$ (j,0))^2
     + (1::rat)^2"
    using terminal_equation
    by simp

  have nonzero:
    "xv1 ≠ 0 ∨
     (∑j∈{0..<𝗏}. x $$ (j,0)) ≠ 0 ∨
     (1::rat) ≠ 0"
    by simp

  show ?thesis
    using brc_minus_from_terminal[
      of xv1
         "∑j∈{0..<𝗏}. x $$ (j,0)"
         "1::rat"]
      terminal_equation_square nonzero
    by blast
qed

definition brc_minus_good_witness ::
  "nat ⇒ nat ⇒ nat ⇒ nat ⇒ nat ⇒ bool" where
  "brc_minus_good_witness a b c d w ⟷
     (∃x :: rat mat. ∃xv1 y0 y1 y2 :: rat.
        brc_minus_prefix_good
          a b c d x xv1 (w - 1) ∧
        y_of
          ((a,b,c,d),
           (brc_extend_x x xv1 $$ (𝗏-3,0),
            brc_extend_x x xv1 $$ (𝗏-2,0),
            brc_extend_x x xv1 $$ (𝗏-1,0),
            brc_extend_x x xv1 $$ (𝗏,0)))
        =
          (y0,y1,y2,1) ∧
        brc_L x (𝗏-3)^2 +
        brc_L x (𝗏-2)^2 +
        brc_L x (𝗏-1)^2
        =
        y0^2 + y1^2 + y2^2)"

lemma brc_minus_equation_from_good_witness_exists:
  fixes a b c d w :: nat
  assumes v_form:
    "𝗏 = 4 * w - 1"
  assumes w_pos:
    "0 < w"
  assumes four_sq:
    "a^2 + b^2 + c^2 + d^2 = 𝗄 - Λ"
  assumes witness:
    "brc_minus_good_witness a b c d w"
  shows
    "brc_minus_equation"
proof -
  obtain x :: "rat mat"
    and xv1 y0 y1 y2 :: rat
    where good:
      "brc_minus_prefix_good
         a b c d x xv1 (w - 1)"
    and tuple:
      "y_of
        ((a,b,c,d),
         (brc_extend_x x xv1 $$ (𝗏-3,0),
          brc_extend_x x xv1 $$ (𝗏-2,0),
          brc_extend_x x xv1 $$ (𝗏-1,0),
          brc_extend_x x xv1 $$ (𝗏,0)))
       =
       (y0,y1,y2,1)"
    and terminal:
      "brc_L x (𝗏-3)^2 +
       brc_L x (𝗏-2)^2 +
       brc_L x (𝗏-1)^2
       =
       y0^2 + y1^2 + y2^2"
    using witness
    unfolding brc_minus_good_witness_def
    by blast

  show ?thesis
    using brc_minus_equation_from_good_witness[
      OF v_form w_pos four_sq good tuple terminal]
    .
qed

definition brc_minus_tail_zero ::
  "rat mat ⇒ nat ⇒ bool" where
  "brc_minus_tail_zero x q ⟷
     (∀h j. h < q ⟶ j < 4 ⟶
        (∑r∈{4 * Suc h..<𝗏}.
           of_int (N $$ (r,4*h+j)) *
           x $$ (r,0)) = 0)"

lemma brc_minus_prefix_goodI:
  assumes eliminated:
    "brc_minus_prefix_eliminated
       a b c d x xv1 q"
  assumes tail_zero:
    "brc_minus_tail_zero x q"
  shows
    "brc_minus_prefix_good
       a b c d x xv1 q"
  using eliminated tail_zero
  unfolding brc_minus_prefix_good_def
    brc_minus_tail_zero_def
  by blast

lemma brc_minus_prefix_goodD_eliminated:
  assumes good:
    "brc_minus_prefix_good
       a b c d x xv1 q"
  shows
    "brc_minus_prefix_eliminated
       a b c d x xv1 q"
  using good
  unfolding brc_minus_prefix_good_def
  by blast

lemma brc_minus_prefix_goodD_tail_zero:
  assumes good:
    "brc_minus_prefix_good
       a b c d x xv1 q"
  shows
    "brc_minus_tail_zero x q"
  using good
  unfolding brc_minus_prefix_good_def
    brc_minus_tail_zero_def
  by blast

lemma brc_minus_good_witness_from_full_elimination:
  fixes a b c d w :: nat
  assumes v_form:
    "𝗏 = 4 * w - 1"
  assumes w_pos:
    "0 < w"
  assumes four_sq:
    "a^2 + b^2 + c^2 + d^2 = 𝗄 - Λ"
  assumes nzsum:
    "a^2 + b^2 + c^2 + d^2 ≠ 0"
  assumes tails:
    "⋀x xv1 y0 y1 y2.
       brc_minus_prefix_eliminated
         a b c d x xv1 (w - 1) ⟹
       y_of
        ((a,b,c,d),
         (brc_extend_x x xv1 $$ (𝗏-3,0),
          brc_extend_x x xv1 $$ (𝗏-2,0),
          brc_extend_x x xv1 $$ (𝗏-1,0),
          brc_extend_x x xv1 $$ (𝗏,0)))
       =
       (y0,y1,y2,1) ⟹
       brc_L x (𝗏-3)^2 +
       brc_L x (𝗏-2)^2 +
       brc_L x (𝗏-1)^2
       =
       y0^2 + y1^2 + y2^2 ⟹
       brc_minus_tail_zero x (w - 1)"
  shows
    "brc_minus_good_witness a b c d w"
proof -
  obtain x :: "rat mat"
    and xv1 y0 y1 y2 :: rat
    where eliminated:
      "brc_minus_prefix_eliminated
         a b c d x xv1 (w - 1)"
    and tuple:
      "y_of
        ((a,b,c,d),
         (brc_extend_x x xv1 $$ (𝗏-3,0),
          brc_extend_x x xv1 $$ (𝗏-2,0),
          brc_extend_x x xv1 $$ (𝗏-1,0),
          brc_extend_x x xv1 $$ (𝗏,0)))
       =
       (y0,y1,y2,1)"
    and terminal:
      "brc_L x (𝗏-3)^2 +
       brc_L x (𝗏-2)^2 +
       brc_L x (𝗏-1)^2
       =
       y0^2 + y1^2 + y2^2"
    using brc_minus_full_elimination_exists[
      OF v_form w_pos four_sq nzsum]
    by blast

  have tail_zero:
    "brc_minus_tail_zero x (w - 1)"
    using tails[OF eliminated tuple terminal] .

  have good:
    "brc_minus_prefix_good
       a b c d x xv1 (w - 1)"
    using brc_minus_prefix_goodI[
      OF eliminated tail_zero]
    .

  show ?thesis
    unfolding brc_minus_good_witness_def
    using good tuple terminal
    by blast
qed

subsection ‹Rational quadratic-form reduction›

definition rat_quadratic_equiv ::
  "('a ⇒ rat) ⇒ ('a ⇒ rat) ⇒ 'a ⇒ bool" where
  "rat_quadratic_equiv Q R z0 ⟷
     (∃f :: 'a ⇒ 'a. ∃g :: 'a ⇒ 'a.
        (∀x. g (f x) = x) ∧
        (∀x. f (g x) = x) ∧
        f z0 = z0 ∧
        g z0 = z0 ∧
        (∀x. Q x = R (f x)))"

definition has_nontrivial_zero ::
  "('a ⇒ rat) ⇒ 'a ⇒ bool" where
  "has_nontrivial_zero Q z0 ⟷
     (∃x. x ≠ z0 ∧ Q x = 0)"

lemma rat_quadratic_equiv_preserves_nontrivial_zero:
  fixes Q R :: "'a ⇒ rat"
  fixes z0 :: 'a
  assumes equiv:
    "rat_quadratic_equiv Q R z0"
  shows
    "has_nontrivial_zero Q z0
     ⟷
     has_nontrivial_zero R z0"
proof -
  obtain f :: "'a ⇒ 'a"
    and g :: "'a ⇒ 'a"
    where gf:
      "∀x. g (f x) = x"
    and fg:
      "∀x. f (g x) = x"
    and f_z0:
      "f z0 = z0"
    and g_z0:
      "g z0 = z0"
    and form:
      "∀x. Q x = R (f x)"
    using equiv
    unfolding rat_quadratic_equiv_def
    by blast

  have forward:
    "has_nontrivial_zero Q z0
     ⟹ has_nontrivial_zero R z0"
  proof -
    assume q_zero:
      "has_nontrivial_zero Q z0"

    obtain x where
      x_nonzero:
        "x ≠ z0"
      and qx:
        "Q x = 0"
      using q_zero
      unfolding has_nontrivial_zero_def
      by blast

    have fx_nonzero:
      "f x ≠ z0"
    proof
      assume fx_zero:
        "f x = z0"

      have "g (f x) = g z0"
        using fx_zero
        by simp

      then have "x = z0"
        using gf g_z0
        by simp

      then show False
        using x_nonzero
        by contradiction
    qed

    have rfx:
      "R (f x) = 0"
      using form qx
      by simp

    show
      "has_nontrivial_zero R z0"
      unfolding has_nontrivial_zero_def
      using fx_nonzero rfx
      by blast
  qed

  have backward:
    "has_nontrivial_zero R z0
     ⟹ has_nontrivial_zero Q z0"
  proof -
    assume r_zero:
      "has_nontrivial_zero R z0"

    obtain y where
      y_nonzero:
        "y ≠ z0"
      and ry:
        "R y = 0"
      using r_zero
      unfolding has_nontrivial_zero_def
      by blast

    have gy_nonzero:
      "g y ≠ z0"
    proof
      assume gy_zero:
        "g y = z0"

      have "f (g y) = f z0"
        using gy_zero
        by simp

      then have "y = z0"
        using fg f_z0
        by simp

      then show False
        using y_nonzero
        by contradiction
    qed

    have qgy:
      "Q (g y) = 0"
    proof -
      have "Q (g y) = R (f (g y))"
        using form
        by blast

      also have "... = R y"
        using fg
        by simp

      also have "... = 0"
        using ry .

      finally show ?thesis .
    qed

    show
      "has_nontrivial_zero Q z0"
      unfolding has_nontrivial_zero_def
      using gy_nonzero qgy
      by blast
  qed

  show ?thesis
    using forward backward
    by blast
qed

lemma rat_quadratic_equiv_sym:
  fixes Q R :: "'a ⇒ rat"
  fixes z0 :: 'a
  assumes equiv:
    "rat_quadratic_equiv Q R z0"
  shows
    "rat_quadratic_equiv R Q z0"
proof -
  obtain f :: "'a ⇒ 'a"
    and g :: "'a ⇒ 'a"
    where gf:
      "∀x. g (f x) = x"
    and fg:
      "∀x. f (g x) = x"
    and f_z0:
      "f z0 = z0"
    and g_z0:
      "g z0 = z0"
    and form:
      "∀x. Q x = R (f x)"
    using equiv
    unfolding rat_quadratic_equiv_def
    by blast

  have reverse_form:
    "∀y. R y = Q (g y)"
  proof
    fix y

    have "Q (g y) = R (f (g y))"
      using form
      by blast

    also have "... = R y"
      using fg
      by simp

    finally show "R y = Q (g y)"
      by simp
  qed

  show ?thesis
    unfolding rat_quadratic_equiv_def
    apply (rule exI[of _ g])
    apply (rule exI[of _ f])
    using fg gf g_z0 f_z0 reverse_form
    apply blast
    done
qed

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

lemma rat_vec_zero_on:
  "rat_vec_on n rat_vec_zero"
  unfolding rat_vec_on_def rat_vec_zero_def
  by simp

lemma rat_diagonal_form_zero:
  fixes c :: "nat ⇒ rat"
  shows
    "rat_diagonal_form n c rat_vec_zero = 0"
  unfolding rat_diagonal_form_def rat_vec_zero_def
  by simp

lemma rat_vec_on_eq_zero_iff:
  assumes support:
    "rat_vec_on n x"
  shows
    "x = rat_vec_zero
     ⟷
     (∀i<n. x i = 0)"
proof
  assume zero:
    "x = rat_vec_zero"

  show "∀i<n. x i = 0"
    using zero
    unfolding rat_vec_zero_def
    by simp
next
  assume inside:
    "∀i<n. x i = 0"

  show "x = rat_vec_zero"
  proof
    fix i

    show "x i = rat_vec_zero i"
    proof (cases "i < n")
      case True
      then have "x i = 0"
        using inside
        by blast
      then show ?thesis
        unfolding rat_vec_zero_def
        by simp
    next
      case False
      then have "n ≤ i"
        by simp
      then have "x i = 0"
        using support
        unfolding rat_vec_on_def
        by blast
      then show ?thesis
        unfolding rat_vec_zero_def
        by simp
    qed
  qed
qed

lemma rat_vec_on_nonzero_iff:
  assumes support:
    "rat_vec_on n x"
  shows
    "x ≠ rat_vec_zero
     ⟷
     (∃i<n. x i ≠ 0)"
proof -
  have
    "x = rat_vec_zero
     ⟷
     (∀i<n. x i = 0)"
    using rat_vec_on_eq_zero_iff[OF support] .

  then show ?thesis
    by blast
qed

definition rat_scale_coordinate ::
  "nat ⇒ rat ⇒ (nat ⇒ rat) ⇒ nat ⇒ rat" where
  "rat_scale_coordinate k u x =
     (λi. if i = k then u * x i else x i)"

lemma rat_scale_coordinate_on:
  assumes support:
    "rat_vec_on n x"
  assumes k_bound:
    "k < n"
  shows
    "rat_vec_on n (rat_scale_coordinate k u x)"
proof -
  show ?thesis
    unfolding rat_vec_on_def rat_scale_coordinate_def
  proof (intro allI impI)
    fix i
    assume n_le:
      "n ≤ i"

    have i_ne:
      "i ≠ k"
      using n_le k_bound
      by simp

    show "(if i = k then u * x i else x i) = 0"
      using support n_le i_ne
      unfolding rat_vec_on_def
      by simp
  qed
qed

lemma rat_scale_coordinate_one:
  "rat_scale_coordinate k 1 x = x"
  unfolding rat_scale_coordinate_def
  by auto

lemma rat_scale_coordinate_zero:
  "rat_scale_coordinate k u rat_vec_zero = rat_vec_zero"
  unfolding rat_scale_coordinate_def rat_vec_zero_def
  by auto

lemma rat_scale_coordinate_inverse:
  assumes u_nz:
    "u ≠ 0"
  shows
    "rat_scale_coordinate k (1/u)
       (rat_scale_coordinate k u x)
     =
     x"
proof
  fix i

  show
    "rat_scale_coordinate k (1/u)
       (rat_scale_coordinate k u x) i
     =
     x i"
  proof (cases "i = k")
    case True
    then show ?thesis
      using u_nz
      unfolding rat_scale_coordinate_def
      by simp
  next
    case False
    then show ?thesis
      unfolding rat_scale_coordinate_def
      by simp
  qed
qed

lemma rat_scale_coordinate_inverse_rev:
  assumes u_nz:
    "u ≠ 0"
  shows
    "rat_scale_coordinate k u
       (rat_scale_coordinate k (1/u) x)
     =
     x"
proof
  fix i

  show
    "rat_scale_coordinate k u
       (rat_scale_coordinate k (1/u) x) i
     =
     x i"
  proof (cases "i = k")
    case True
    then show ?thesis
      using u_nz
      unfolding rat_scale_coordinate_def
      by simp
  next
    case False
    then show ?thesis
      unfolding rat_scale_coordinate_def
      by simp
  qed
qed

lemma rat_diagonal_form_scale_coordinate:
  fixes c :: "nat ⇒ rat"
  assumes k_bound:
    "k < n"
  shows
    "rat_diagonal_form n c
       (rat_scale_coordinate k u x)
     =
     rat_diagonal_form n
       (λi. if i = k then c i * u^2 else c i)
       x"
proof -
  show ?thesis
    unfolding rat_diagonal_form_def
      rat_scale_coordinate_def
    apply (rule sum.cong)
     apply (rule refl)
    using k_bound
    apply (simp add: power2_eq_square algebra_simps)
    done
qed

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

lemma rat_match_substitution_other:
  assumes ji:
    "j ≠ i"
  shows
    "rat_match_substitution n i c y j = y j"
  using ji
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

lemma rat_match_substitution_on:
  assumes support:
    "rat_vec_on n y"
  assumes i_bound:
    "i < n"
  shows
    "rat_vec_on n
       (rat_match_substitution n i c y)"
proof -
  show ?thesis
    unfolding rat_vec_on_def
  proof (intro allI impI)
    fix j
    assume n_le:
      "n ≤ j"

    have ji:
      "j ≠ i"
      using n_le i_bound
      by auto

    have yj:
      "y j = 0"
      using support n_le
      unfolding rat_vec_on_def
      by blast

    show
      "rat_match_substitution n i c y j = 0"
      using ji yj
      unfolding rat_match_substitution_def
      by simp
  qed
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

lemma rat_eliminate_unit_coordinate:
  fixes c d :: "nat ⇒ rat"
  fixes Q :: "(nat ⇒ rat) ⇒ rat"
  assumes i_bound:
    "i < n"
  assumes unit_coeff:
    "d i = 1"
  assumes identity:
    "⋀x.
       (rat_linear_form n c x)^2 + Q x
       =
       rat_diagonal_form n d x"
  shows
    "Q (rat_match_substitution n i c y)
     =
     (∑j∈{0..<n} - {i}.
        d j * (y j)^2)"
proof -
  let ?z =
    "rat_match_substitution n i c y"

  have instantiated:
    "(rat_linear_form n c ?z)^2 + Q ?z
     =
     rat_diagonal_form n d ?z"
    using identity[of ?z] .

  have cancellation:
    "rat_diagonal_form n d ?z -
       (rat_linear_form n c ?z)^2
     =
     (∑j∈{0..<n} - {i}.
        d j * (y j)^2)"
    using rat_match_substitution_cancels_coordinate[
      where n = n
        and i = i
        and c = c
        and d = d
        and y = y,
      OF i_bound unit_coeff]
    .

  show ?thesis
    using instantiated cancellation
    by linarith
qed

lemma rat_match_substitution_independent_at:
  assumes agree:
    "⋀j. j ≠ i ⟹ y j = y' j"
  shows
    "rat_match_substitution n i c y
     =
     rat_match_substitution n i c y'"
proof -
  have rest:
    "rat_linear_rest n i c y
     =
     rat_linear_rest n i c y'"
  proof -
    show ?thesis
      unfolding rat_linear_rest_def
      apply (rule sum.cong)
       apply (rule refl)
      using agree
      by auto
  qed

  show ?thesis
  proof
    fix j

    show
      "rat_match_substitution n i c y j
       =
       rat_match_substitution n i c y' j"
    proof (cases "j = i")
      case True
      then show ?thesis
        unfolding rat_match_substitution_def
        using rest
        by simp
    next
      case False
      then show ?thesis
        unfolding rat_match_substitution_def
        using agree[OF False]
        by simp
    qed
  qed
qed

definition rat_zero_coordinate ::
  "nat ⇒ (nat ⇒ rat) ⇒ nat ⇒ rat" where
  "rat_zero_coordinate i y =
     (λj. if j = i then 0 else y j)"

lemma rat_match_substitution_zero_coordinate:
  "rat_match_substitution n i c
      (rat_zero_coordinate i y)
   =
   rat_match_substitution n i c y"
proof -
  show ?thesis
    using rat_match_substitution_independent_at[
      where n = n
        and i = i
        and c = c
        and y = "rat_zero_coordinate i y"
        and y' = y]
    unfolding rat_zero_coordinate_def
    by simp
qed

lemma rat_zero_coordinate_on:
  assumes support:
    "rat_vec_on n y"
  shows
    "rat_vec_on n (rat_zero_coordinate i y)"
proof -
  show ?thesis
    unfolding rat_vec_on_def rat_zero_coordinate_def
  proof (intro allI impI)
    fix j
    assume n_le:
      "n ≤ j"

    have yj:
      "y j = 0"
      using support n_le
      unfolding rat_vec_on_def
      by blast

    show "(if j = i then 0 else y j) = 0"
      using yj
      by simp
  qed
qed

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

lemma rat_eliminate_unit_coordinate_canonical:
  fixes c d :: "nat ⇒ rat"
  fixes Q :: "(nat ⇒ rat) ⇒ rat"
  assumes i_bound:
    "i < n"
  assumes unit_coeff:
    "d i = 1"
  assumes identity:
    "⋀x.
       (rat_linear_form n c x)^2 + Q x
       =
       rat_diagonal_form n d x"
  shows
    "Q (rat_match_substitution n i c y)
     =
     rat_diagonal_form n d
       (rat_zero_coordinate i y)"
proof -
  have eliminated:
    "Q (rat_match_substitution n i c y)
     =
     (∑j∈{0..<n} - {i}.
        d j * (y j)^2)"
    using rat_eliminate_unit_coordinate[
      where n = n
        and i = i
        and c = c
        and d = d
        and Q = Q
        and y = y,
      OF i_bound unit_coeff identity]
    .

  have diagonal:
    "rat_diagonal_form n d
       (rat_zero_coordinate i y)
     =
     (∑j∈{0..<n} - {i}.
        d j * (y j)^2)"
    using rat_diagonal_form_zero_coordinate[
      where n = n
        and i = i
        and d = d
        and y = y,
      OF i_bound]
    .

  show ?thesis
    using eliminated diagonal
    by simp
qed

lemma brc_match_y_linear:
  "brc_match_y A (B * y)
   =
   brc_match_coeff A B * y"
proof -
  have affine:
    "brc_match_y A (B * y + 0)
     =
     brc_match_coeff A B * y +
     brc_match_y A 0"
    using brc_match_y_affine[
      where A = A
        and B = B
        and y = y
        and R = 0]
    .

  have zero:
    "brc_match_y A 0 = 0"
    unfolding brc_match_y_def
    by simp

  show ?thesis
    using affine zero
    by simp
qed

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

lemma rat_match_pullback_coeff_at:
  "rat_match_pullback_coeff n i c e i = 0"
  unfolding rat_match_pullback_coeff_def
  by simp

lemma rat_match_pullback_coeff_other:
  assumes ji:
    "j ≠ i"
  shows
    "rat_match_pullback_coeff n i c e j
     =
     e j +
     e i * brc_match_coeff (c i) (c j)"
  using ji
  unfolding rat_match_pullback_coeff_def
  by simp

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

definition rat_sum_linear_squares ::
  "nat ⇒ nat ⇒
   (nat ⇒ nat ⇒ rat) ⇒
   (nat ⇒ rat) ⇒ rat" where
  "rat_sum_linear_squares n m C y =
     (∑r∈{0..<m}.
        (rat_linear_form n (C r) y)^2)"

lemma rat_sum_linear_squares_zero:
  "rat_sum_linear_squares n m C rat_vec_zero = 0"
proof -
  have form_zero:
    "rat_linear_form n (C r) rat_vec_zero = 0"
    for r
    unfolding rat_linear_form_def rat_vec_zero_def
    by simp

  show ?thesis
    unfolding rat_sum_linear_squares_def
    using form_zero
    by simp
qed

lemma rat_sum_linear_squares_match_substitution:
  fixes c :: "nat ⇒ rat"
  fixes C :: "nat ⇒ nat ⇒ rat"
  assumes i_bound:
    "i < n"
  shows
    "rat_sum_linear_squares n m C
       (rat_match_substitution n i c y)
     =
     rat_sum_linear_squares n m
       (λr.
          rat_match_pullback_coeff
            n i c (C r))
       y"
proof -
  show ?thesis
    unfolding rat_sum_linear_squares_def
  proof (rule sum.cong)
    show "{0..<m} = {0..<m}"
      by simp
  next
    fix r
    assume r_mem:
      "r ∈ {0..<m}"

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
      "(rat_linear_form n (C r)
          (rat_match_substitution n i c y))^2
       =
       (rat_linear_form n
          (rat_match_pullback_coeff
            n i c (C r))
          y)^2"
      using form
      by simp
  qed
qed

lemma rat_eliminate_head_linear_square:
  fixes c d :: "nat ⇒ rat"
  fixes C :: "nat ⇒ nat ⇒ rat"
  assumes i_bound:
    "i < n"
  assumes unit_coeff:
    "d i = 1"
  assumes identity:
    "⋀x.
       (rat_linear_form n c x)^2 +
       rat_sum_linear_squares n m C x
       =
       rat_diagonal_form n d x"
  shows
    "rat_sum_linear_squares n m
       (λr.
          rat_match_pullback_coeff
            n i c (C r))
       y
     =
     rat_diagonal_form n d
       (rat_zero_coordinate i y)"
proof -
  let ?z =
    "rat_match_substitution n i c y"

  have eliminated:
    "rat_sum_linear_squares n m C ?z
     =
     rat_diagonal_form n d
       (rat_zero_coordinate i y)"
    using rat_eliminate_unit_coordinate_canonical[
      where n = n
        and i = i
        and c = c
        and d = d
        and Q = "rat_sum_linear_squares n m C"
        and y = y,
      OF i_bound unit_coeff identity]
    .

  have transformed:
    "rat_sum_linear_squares n m C ?z
     =
     rat_sum_linear_squares n m
       (λr.
          rat_match_pullback_coeff
            n i c (C r))
       y"
    using rat_sum_linear_squares_match_substitution[
      where n = n
        and m = m
        and i = i
        and c = c
        and C = C
        and y = y,
      OF i_bound]
    .

  show ?thesis
    using eliminated transformed
    by simp
qed

definition rat_sum_linear_squares_from ::
  "nat ⇒ nat ⇒ nat ⇒
   (nat ⇒ nat ⇒ rat) ⇒
   (nat ⇒ rat) ⇒ rat" where
  "rat_sum_linear_squares_from n q m C y =
     (∑r∈{q..<m}.
        (rat_linear_form n (C r) y)^2)"

lemma rat_sum_linear_squares_from_zero:
  "rat_sum_linear_squares_from n 0 m C y
   =
   rat_sum_linear_squares n m C y"
  unfolding rat_sum_linear_squares_from_def
    rat_sum_linear_squares_def
  by simp

lemma rat_sum_linear_squares_from_split:
  assumes q_lt:
    "q < m"
  shows
    "rat_sum_linear_squares_from n q m C y
     =
     (rat_linear_form n (C q) y)^2 +
     rat_sum_linear_squares_from
       n (Suc q) m C y"
proof -
  have interval:
    "{q..<m} = insert q {Suc q..<m}"
    using q_lt
    by auto

  have q_not_mem:
    "q ∉ {Suc q..<m}"
    by simp

  show ?thesis
    unfolding rat_sum_linear_squares_from_def
    using interval q_not_mem
    by simp
qed

lemma rat_sum_linear_squares_from_match:
  fixes c :: "nat ⇒ rat"
  fixes C :: "nat ⇒ nat ⇒ rat"
  assumes i_bound:
    "i < n"
  shows
    "rat_sum_linear_squares_from n q m C
       (rat_match_substitution n i c y)
     =
     rat_sum_linear_squares_from n q m
       (λr.
          rat_match_pullback_coeff
            n i c (C r))
       y"
proof -
  show ?thesis
    unfolding rat_sum_linear_squares_from_def
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
      "(rat_linear_form n (C r)
          (rat_match_substitution n i c y))^2
       =
       (rat_linear_form n
          (rat_match_pullback_coeff
            n i c (C r))
          y)^2"
      using form
      by simp
  qed
qed

definition rat_elimination_update ::
  "nat ⇒ nat ⇒
   (nat ⇒ nat ⇒ rat) ⇒
   nat ⇒ nat ⇒ rat" where
  "rat_elimination_update n q C =
     (λr.
        rat_match_pullback_coeff
          n q (C q) (C r))"

lemma rat_elimination_update_form:
  assumes q_bound:
    "q < n"
  shows
    "rat_linear_form n (C r)
       (rat_match_substitution n q (C q) y)
     =
     rat_linear_form n
       (rat_elimination_update n q C r)
       y"
proof -
  show ?thesis
    unfolding rat_elimination_update_def
    using rat_linear_form_match_substitution[
      where n = n
        and i = q
        and c = "C q"
        and e = "C r"
        and y = y,
      OF q_bound]
    .
qed

lemma rat_elimination_update_zero:
  "rat_elimination_update n q C r q = 0"
  unfolding rat_elimination_update_def
    rat_match_pullback_coeff_def
  by simp

primrec rat_elimination_coeffs ::
  "nat ⇒ nat ⇒
   (nat ⇒ nat ⇒ rat) ⇒
   nat ⇒ nat ⇒ rat" where
  "rat_elimination_coeffs n 0 C = C"
| "rat_elimination_coeffs n (Suc q) C =
     rat_elimination_update
       n q
       (rat_elimination_coeffs n q C)"

lemma rat_elimination_coeffs_Suc:
  "rat_elimination_coeffs n (Suc q) C r
   =
   rat_match_pullback_coeff
     n q
     (rat_elimination_coeffs n q C q)
     (rat_elimination_coeffs n q C r)"
  by (simp add: rat_elimination_update_def)

lemma rat_elimination_coeffs_new_zero:
  "rat_elimination_coeffs n (Suc q) C r q = 0"
  by (simp add:
      rat_elimination_update_def
      rat_match_pullback_coeff_def)

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

lemma rat_zero_prefix_zero:
  "rat_zero_prefix 0 y = y"
  unfolding rat_zero_prefix_def
  by auto

lemma rat_zero_prefix_Suc:
  "rat_zero_prefix (Suc q) y
   =
   rat_zero_coordinate q
     (rat_zero_prefix q y)"
proof
  fix j

  show
    "rat_zero_prefix (Suc q) y j
     =
     rat_zero_coordinate q
       (rat_zero_prefix q y) j"
    unfolding rat_zero_prefix_def
      rat_zero_coordinate_def
    by auto
qed

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

lemma rat_sum_from_elimination_zero_prefix:
  "rat_sum_linear_squares_from
     n q m
     (rat_elimination_coeffs n q C)
     (rat_zero_prefix q y)
   =
   rat_sum_linear_squares_from
     n q m
     (rat_elimination_coeffs n q C)
     y"
proof -
  show ?thesis
    unfolding rat_sum_linear_squares_from_def
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
      "(rat_linear_form n
          (rat_elimination_coeffs n q C r)
          (rat_zero_prefix q y))^2
       =
       (rat_linear_form n
          (rat_elimination_coeffs n q C r)
          y)^2"
      using form
      by simp
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

lemma rat_elimination_stage_step:
  fixes C :: "nat ⇒ nat ⇒ rat"
  fixes d :: "nat ⇒ rat"
  assumes q_lt_m:
    "q < m"
  assumes q_lt_n:
    "q < n"
  assumes unit:
    "d q = 1"
  assumes stage:
    "⋀x.
       rat_sum_linear_squares_from
         n q m
         (rat_elimination_coeffs n q C) x
       =
       rat_diagonal_form n d
         (rat_zero_prefix q x)"
  shows
    "⋀y.
       rat_sum_linear_squares_from
         n (Suc q) m
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
    "rat_sum_linear_squares_from
       n q m ?D ?z
     =
     rat_diagonal_form n d ?z"
    using stage[of ?z] z_prefix
    by simp

  have split:
    "rat_sum_linear_squares_from
       n q m ?D ?z
     =
     (rat_linear_form n (?D q) ?z)^2 +
     rat_sum_linear_squares_from
       n (Suc q) m ?D ?z"
    using rat_sum_linear_squares_from_split[
      where n = n
        and q = q
        and m = m
        and C = ?D
        and y = ?z,
      OF q_lt_m]
    .

  have remaining:
    "rat_sum_linear_squares_from
       n (Suc q) m ?D ?z
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
    "rat_sum_linear_squares_from
       n (Suc q) m ?D ?z
     =
     rat_sum_linear_squares_from
       n (Suc q) m
       (rat_elimination_coeffs n (Suc q) C)
       ?u"
    using rat_sum_linear_squares_from_match[
      where n = n
        and q = "Suc q"
        and m = m
        and i = q
        and c = ?p
        and C = ?D
        and y = ?u,
      OF q_lt_n]
    by (simp add: rat_elimination_update_def)

  have at_u:
    "rat_sum_linear_squares_from
       n (Suc q) m
       (rat_elimination_coeffs n (Suc q) C)
       ?u
     =
     rat_diagonal_form n d ?u"
    using remaining cancellation diagonal_u transformed
    by simp

  have remove_prefix:
    "rat_sum_linear_squares_from
       n (Suc q) m
       (rat_elimination_coeffs n (Suc q) C)
       ?u
     =
     rat_sum_linear_squares_from
       n (Suc q) m
       (rat_elimination_coeffs n (Suc q) C)
       y"
    using rat_sum_from_elimination_zero_prefix[
      where n = n
        and q = "Suc q"
        and m = m
        and C = C
        and y = y]
    .

  show
    "rat_sum_linear_squares_from
       n (Suc q) m
       (rat_elimination_coeffs n (Suc q) C) y
     =
     rat_diagonal_form n d
       (rat_zero_prefix (Suc q) y)"
    using at_u remove_prefix
    by simp
qed

lemma rat_elimination_iterate:
  fixes C :: "nat ⇒ nat ⇒ rat"
  fixes d :: "nat ⇒ rat"
  assumes Q_le_m:
    "Q ≤ m"
  assumes Q_le_n:
    "Q ≤ n"
  assumes units:
    "⋀q. q < Q ⟹ d q = 1"
  assumes initial:
    "⋀x.
       rat_sum_linear_squares_from n 0 m C x
       =
       rat_diagonal_form n d x"
  shows
    "⋀y.
       rat_sum_linear_squares_from
         n Q m
         (rat_elimination_coeffs n Q C) y
       =
       rat_diagonal_form n d
         (rat_zero_prefix Q y)"
  using Q_le_m Q_le_n units
proof (induction Q)
  case 0

  fix y

  have initial_y:
    "rat_sum_linear_squares_from n 0 m C y
     =
     rat_diagonal_form n d y"
    using initial[of y] .

  show
    "rat_sum_linear_squares_from
       n 0 m
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

  have units_Q:
    "⋀q. q < Q ⟹ d q = 1"
    using Suc.prems(3)
    by simp

  have stage_Q:
    "⋀x.
       rat_sum_linear_squares_from
         n Q m
         (rat_elimination_coeffs n Q C) x
       =
       rat_diagonal_form n d
         (rat_zero_prefix Q x)"
    using Suc.IH[OF Q_le_m Q_le_n units_Q] .

  have Q_lt_m:
    "Q < m"
    using Suc.prems(1)
    by simp

  have Q_lt_n:
    "Q < n"
    using Suc.prems(2)
    by simp

  have unit_Q:
    "d Q = 1"
    using Suc.prems(3)
    by simp

  show ?case
    using rat_elimination_stage_step[
      where n = n
        and q = Q
        and m = m
        and C = C
        and d = d,
      OF Q_lt_m Q_lt_n unit_Q stage_Q]
    .
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

lemma rat_linear_form_unit_coordinate:
  assumes k_bound:
    "k < n"
  shows
    "rat_linear_form n c
       (rat_unit_coordinate k)
     =
     c k"
proof -
  have k_mem:
    "k ∈ {0..<n}"
    using k_bound
    by simp

  show ?thesis
    unfolding rat_linear_form_def
      rat_unit_coordinate_def
    using k_mem
    by (simp add: sum.remove)
qed

lemma rat_unit_coordinate_at:
  "rat_unit_coordinate k k = 1"
  unfolding rat_unit_coordinate_def
  by simp

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

lemma rat_basis_expansion_outside:
  assumes n_le:
    "n ≤ t"
  shows
    "rat_basis_expansion n y t = 0"
proof -
  show ?thesis
    unfolding rat_basis_expansion_def
      rat_unit_coordinate_def
    using n_le
    by (intro sum.neutral) auto
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

lemma odd_mod_four_cases:
  assumes odd_v:
    "odd 𝗏"
  shows
    "𝗏 mod 4 = 1 ∨ 𝗏 mod 4 = 3"
proof -
  have bound:
    "𝗏 mod 4 < 4"
    by simp

  have v_mod_two:
    "𝗏 mod 2 = 1"
    using odd_v
    by (simp add: odd_iff_mod_2_eq_one)

  have rem_mod_two:
    "(𝗏 mod 4) mod 2 = 𝗏 mod 2"
    by (simp add: mod_mod_cancel)

  have rem_two:
    "(𝗏 mod 4) mod 2 = 1"
    using v_mod_two rem_mod_two
    by simp

  show ?thesis
    using bound rem_two
    by presburger
qed

lemma bruck_ryser_chowla_odd_rat_cases:
  assumes odd_v:
    "odd 𝗏"
  shows
    "(∃x y z :: rat.
       (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧
       x^2 =
         of_nat (𝗄 - Λ) * y^2 +
         of_nat Λ * z^2)
     ∨
     (∃x y z :: rat.
       (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧
       x^2 =
         of_nat (𝗄 - Λ) * y^2 -
         of_nat Λ * z^2)"
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

    have plus:
      "∃x y z :: rat.
         (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧
         x^2 =
           of_nat (𝗄 - Λ) * y^2 +
           of_nat Λ * z^2"
      using brc_plus_rational_solution_exists[
        OF v_form]
      .

    show ?thesis
      using plus
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

    have minus:
      "∃x y z :: rat.
         (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧
         x^2 =
           of_nat (𝗄 - Λ) * y^2 -
           of_nat Λ * z^2"
      using brc_minus_rational_solution_exists[
        OF v_form w_pos]
      .

    show ?thesis
      using minus
      by blast
  qed
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

lemma bruck_ryser_chowla_odd_int_cases:
  assumes odd_v:
    "odd 𝗏"
  shows
    "(∃x y z :: int.
       (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧
       x^2 =
         int (𝗄 - Λ) * y^2 +
         int Λ * z^2)
     ∨
     (∃x y z :: int.
       (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧
       x^2 =
         int (𝗄 - Λ) * y^2 -
         int Λ * z^2)"
proof -
  have rational_cases:
    "(∃x y z :: rat.
       (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧
       x^2 =
         of_nat (𝗄 - Λ) * y^2 +
         of_nat Λ * z^2)
     ∨
     (∃x y z :: rat.
       (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧
       x^2 =
         of_nat (𝗄 - Λ) * y^2 -
         of_nat Λ * z^2)"
    using bruck_ryser_chowla_odd_rat_cases[
      OF odd_v]
    .

  from rational_cases show ?thesis
  proof
    assume plus:
      "∃x y z :: rat.
       (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧
       x^2 =
         of_nat (𝗄 - Λ) * y^2 +
         of_nat Λ * z^2"

    obtain x y z :: rat where nz:
      "x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0"
      and eq:
      "x^2 =
       of_nat (𝗄 - Λ) * y^2 +
       of_nat Λ * z^2"
      using plus
      by blast

    have eq_int_cast:
      "x^2 =
       of_int (int (𝗄 - Λ)) * y^2 +
       of_int (int Λ) * z^2"
      using eq
      by simp

    obtain X Y Z :: int where int_nz:
      "X ≠ 0 ∨ Y ≠ 0 ∨ Z ≠ 0"
      and int_eq:
      "X^2 =
       int (𝗄 - Λ) * Y^2 +
       int Λ * Z^2"
      using rat_quadratic_solution_to_int[
        where A = "int (𝗄 - Λ)"
          and B = "int Λ"
          and x = x and y = y and z = z,
        OF nz eq_int_cast]
      by blast

    show ?thesis
      using int_nz int_eq
      by blast
  next
    assume minus:
      "∃x y z :: rat.
       (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧
       x^2 =
         of_nat (𝗄 - Λ) * y^2 -
         of_nat Λ * z^2"

    obtain x y z :: rat where nz:
      "x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0"
      and eq:
      "x^2 =
       of_nat (𝗄 - Λ) * y^2 -
       of_nat Λ * z^2"
      using minus
      by blast

    have eq_int_cast:
      "x^2 =
       of_int (int (𝗄 - Λ)) * y^2 +
       of_int (- int Λ) * z^2"
      using eq
      by simp

    obtain X Y Z :: int where int_nz:
      "X ≠ 0 ∨ Y ≠ 0 ∨ Z ≠ 0"
      and int_eq_raw:
      "X^2 =
       int (𝗄 - Λ) * Y^2 +
       (- int Λ) * Z^2"
      using rat_quadratic_solution_to_int[
        where A = "int (𝗄 - Λ)"
          and B = "- int Λ"
          and x = x and y = y and z = z,
        OF nz eq_int_cast]
      by blast

    have int_eq:
      "X^2 =
       int (𝗄 - Λ) * Y^2 -
       int Λ * Z^2"
      using int_eq_raw
      by simp

    show ?thesis
      using int_nz int_eq
      by blast
  qed
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
