theory pnt_2
imports
  "pnt.pnt"
begin

notation has_contour_integral (infixr "#~\<integral>" 50)
notation contour_integrable_on (infixr "\<llangle>~\<integral>\<rrangle>" 50)
notation contour_integral ("~\<integral>")
notation pi ("\<pi>")

theorem powr_has_integral:
  fixes a b w :: \<real>
  assumes Hab: "a \<le> b" and Hw: "w > 0 \<and> w \<noteq> 1"
  shows "((\<lambda>x. w ᣔ x) #\<integral> w ᣔ b / ln w - w ᣔ a / ln w) {a..b}"
proof (rule fundamental_theorem_of_calculus)
  show "a \<le> b" using assms by auto
next
  fix x assume "x \<in> {a..b}"
  have "((\<lambda>x. exp (x * ln w)) #vd exp (x * ln w) * (1 * ln w)) (at x within {a..b})"
    by (subst has_real_derivative_iff_has_vector_derivative [symmetric])
       (rule derivative_intros DERIV_cmult_right)+
  hence "((ᣔ) w #vd w ᣔ x * ln w) (at x within {a..b})"
    unfolding powr_def using Hw by (simp add: DERIV_fun_exp)
  moreover have "ln w \<noteq> 0" using Hw by auto
  ultimately show "((\<lambda>x. w ᣔ x / ln w) #vd w ᣔ x) (at x within {a..b})"
    by (auto intro: derivative_eq_intros)
qed

theorem powr_integrable:
  fixes a b w :: \<real>
  assumes Hab: "a \<le> b" and Hw: "w > 0 \<and> w \<noteq> 1"
  shows "(\<lambda>x. w ᣔ x) \<llangle>\<integral>\<rrangle> {a..b}"
by (rule has_integral_integrable, rule powr_has_integral)
   (use assms in auto)

theorem powr_integral_bound_gt_1:
  fixes a b w :: \<real>
  assumes Hab: "a \<le> b" and Hw: "w > 1"
  shows "\<integral> {a..b} (\<lambda>x. w ᣔ x) \<le> w ᣔ b / \<bar>ln w\<bar>"
proof -
  have "\<integral> {a..b} (\<lambda>x. w ᣔ x) = w ᣔ b / ln w - w ᣔ a / ln w"
    by (intro integral_unique powr_has_integral) (use assms in auto)
  also have "\<dots> \<le> w ᣔ b / \<bar>ln w\<bar>" using Hw by auto
  finally show ?thesis .
qed

theorem powr_integral_bound_lt_1:
  fixes a b w :: \<real>
  assumes Hab: "a \<le> b" and Hw: "0 < w \<and> w < 1"
  shows "\<integral> {a..b} (\<lambda>x. w ᣔ x) \<le> w ᣔ a / \<bar>ln w\<bar>"
proof -
  have "\<integral> {a..b} (\<lambda>x. w ᣔ x) = w ᣔ b / ln w - w ᣔ a / ln w"
    by (intro integral_unique powr_has_integral) (use assms in auto)
  also have "\<dots> \<le> w ᣔ a / \<bar>ln w\<bar>" using Hw by (auto simp add: field_simps)
  finally show ?thesis .
qed

theorem powr_mono_lt_1_cancel:
  fixes x a b :: \<real>
  assumes Hx: "0 < x \<and> x < 1"
  shows "(x ᣔ a \<le> x ᣔ b) = (b \<le> a)"
proof -
  have "(x ᣔ a \<le> x ᣔ b) = ((x ᣔ -1) ᣔ -a \<le> (x ᣔ -1) ᣔ -b)" by (simp add: powr_powr)
  also have "\<dots> = (-a \<le> -b)" using Hx by (intro powr_le_cancel_iff) (auto simp add: powr_neg_one)
  also have "\<dots> = (b \<le> a)" by auto
  finally show ?thesis .
qed

theorem integral_linepath_same_Re:
  assumes Ha: "Re a = Re b"
    and Hb: "Im a < Im b"
    and Hf: "(f #~\<integral> x) (linepath a b)"
  shows "((\<lambda>t. f (\<complex> (Re a) t) * \<i>) #\<integral> x) {Im a..Im b}"
proof -
  define path where "path \<equiv> linepath a b"
  define c d e g where "c \<equiv> Re a" and "d \<equiv> Im a" and "e \<equiv> Im b" and "g \<equiv> e - d"
  hence [simp]: "a = \<complex> c d" "b = \<complex> c e" by auto (subst Ha, auto)
  have hg: "0 < g" unfolding g_def using Hb by auto
  have [simp]: "a *\<^sub>R z = a * z" for a and z :: \<complex> by (rule complex_eqI) auto
  have "((\<lambda>t. f (path t) * (b - a)) #\<integral> x) {0..1}"
    unfolding path_def by (subst has_contour_integral_linepath [symmetric]) (intro Hf)
  moreover have "path t = \<complex> c (g *\<^sub>R t + d)" for t
    unfolding path_def linepath_def g_def
    by (auto simp add: field_simps legacy_Complex_simps)
  moreover have "b - a = g * \<i>"
    unfolding g_def by (auto simp add: legacy_Complex_simps)
  ultimately have
    "((\<lambda>t. f (\<complex> c (g *\<^sub>R t + d)) * (g * \<i>)) #\<integral> g * x /\<^sub>R g ^ DIM(\<real>))
     (cbox ((d - d) /\<^sub>R g) ((e - d) /\<^sub>R g))"
    by (subst (6) g_def) (auto simp add: field_simps)
  hence "((\<lambda>t. f (\<complex> c t) * \<i> * g) #\<integral> x * g) {d..e}"
    by (subst (asm) has_integral_affinity_iff)
       (auto simp add: field_simps hg)
  hence "((\<lambda>t. f (\<complex> c t) * \<i> * g * (1 / g)) #\<integral> x * g * (1 / g)) {d..e}"
    by (rule has_integral_mult_left)
  thus ?thesis using hg by auto
qed

theorem perron_aux_3':
  fixes f :: "\<complex> \<Rightarrow> \<complex>" and a b B T :: \<real>
  assumes Ha: "0 < a" and Hb: "0 < b" and hT: "0 < T"
    and Hf: "\<And>t. t \<in> {-T..T} \<Longrightarrow> ║f (\<complex> b t)║ \<le> B"
    and Hf': "(\<lambda>s. f s * a ᣔ s / s) \<llangle>~\<integral>\<rrangle> (linepath (\<complex> b (-T)) (\<complex> b T))"
  shows "║1 / (2*\<pi>*\<i>) * ~\<integral> (linepath (\<complex> b (-T)) (\<complex> b T)) (\<lambda>s. f s * a ᣔ s / s)║
       \<le> B * a ᣔ b * ln (1 + T / b)"
proof -
  define path where "path \<equiv> linepath (\<complex> b (-T)) (\<complex> b T)"
  define t' where "t' t \<equiv> \<complex> (Re (\<complex> b (-T))) t" for t
  define g where "g t \<equiv> f (\<complex> b t) * a ᣔ (\<complex> b t) / \<complex> b t * \<i>" for t
  have hB: "0 \<le> B" using Hf [of 0] hT by (auto, smt (verit) norm_ge_zero)
  have "((\<lambda>t. f (t' t) * a ᣔ (t' t) / (t' t) * \<i>)
        #\<integral> ~\<integral> path (\<lambda>s. f s * a ᣔ s / s)) {Im (\<complex> b (-T))..Im (\<complex> b T)}"
    unfolding t'_def using hT
    by (intro integral_linepath_same_Re, unfold path_def)
       (auto intro: has_contour_integral_integral Hf')
  hence h_int: "(g #\<integral> ~\<integral> path (\<lambda>s. f s * a ᣔ s / s)) {-T..T}" unfolding g_def t'_def by auto
  hence int: "g \<llangle>\<integral>\<rrangle> {-T..T}" by (rule has_integral_integrable)
  have "~\<integral> path (\<lambda>s. f s * a ᣔ s / s) = \<integral> {-T..T} g" using h_int by (rule integral_unique [symmetric])
  also have "║\<dots>║ \<le> \<integral> {-T..T} (\<lambda>t. 2 * B * a ᣔ b / (b + \<bar>t\<bar>))"
  proof (rule integral_norm_bound_integral, goal_cases)
    case 1 from int show ?case .
    case 2 show ?case
      by (intro integrable_continuous_interval continuous_intros)
         (use Hb in auto)
  next
    fix t assume *: "t \<in> {-T..T}"
    have "(b + \<bar>t\<bar>)\<^sup>2 - 4 * (b\<^sup>2 + t\<^sup>2) = - 3 * (b - \<bar>t\<bar>)\<^sup>2 + - 4 * b * \<bar>t\<bar>"
      by (simp add: field_simps power2_eq_square)
    also have "\<dots> \<le> 0" using Hb by (intro add_nonpos_nonpos) auto
    finally have "(b + \<bar>t\<bar>)\<^sup>2 - 4 * (b\<^sup>2 + t\<^sup>2) \<le> 0" .
    hence "b + \<bar>t\<bar> \<le> 2 * ║\<complex> b t║"
      unfolding cmod_def by (rule_tac power2_le_imp_le) auto
    hence "a ᣔ b / ║\<complex> b t║ \<le> a ᣔ b / ((b + \<bar>t\<bar>) / 2)"
      using Hb by (intro divide_left_mono) (auto intro!: mult_pos_pos)
    hence "a ᣔ b / ║\<complex> b t║ * ║f (\<complex> b t)║ \<le> a ᣔ b / ((b + \<bar>t\<bar>) / 2) * B"
      by (insert Hf [OF *], rule mult_mono) (use Hb in auto)
    thus "║g t║ \<le> 2 * B * a ᣔ b / (b + \<bar>t\<bar>)"
      unfolding g_def
      by (auto simp add: norm_mult norm_divide)
         (subst norm_powr_real_powr, insert Ha, auto simp add: mult_ac)
  qed
  also have "\<dots> = 2 * B * a ᣔ b * \<integral> {-T..T} (\<lambda>t. 1 / (b + \<bar>t\<bar>))"
    by (subst divide_inverse, subst integral_mult_right) (simp add: inverse_eq_divide)
  also have "\<dots> = 4 * B * a ᣔ b * \<integral> {0..T} (\<lambda>t. 1 / (b + \<bar>t\<bar>))"
  proof -
    let ?f = "\<lambda>t. 1 / (b + \<bar>t\<bar>)"
    have "\<integral> {-T..0} ?f + \<integral> {0..T} ?f = \<integral> {-T..T} ?f"
      by (intro integral_combine integrable_continuous_interval continuous_intros)
         (use Hb hT in auto)
    moreover have "\<integral> {-T..-0} (\<lambda>t. ?f (-t)) = \<integral> {0..T} ?f" by (rule integral_reflect_real)
    hence "\<integral> {-T..0} ?f = \<integral> {0..T} ?f" by auto
    ultimately show ?thesis by auto
  qed
  also have "\<dots> = 4 * B * a ᣔ b * ln (1 + T / b)"
  proof -
    have "((\<lambda>t. 1 / (b + \<bar>t\<bar>)) #\<integral> (ln (b + T) - ln (b + 0))) {0..T}"
    proof (rule fundamental_theorem_of_calculus, goal_cases)
      case 1 show ?case using hT by auto
    next
      fix x assume *: "x \<in> {0..T}"
      have "((\<lambda>x. ln (b + x)) #rd 1 / (b + x) * (0 + 1)) (at x within {0..T})"
        by (intro derivative_intros) (use Hb * in auto)
      thus "((\<lambda>x. ln (b + x)) #vd 1 / (b + \<bar>x\<bar>)) (at x within {0..T})"
        using * by (subst has_real_derivative_iff_has_vector_derivative [symmetric]) auto
    qed
    moreover have "ln (b + T) - ln (b + 0) = ln (1 + T / b)"
      using Hb hT by (subst ln_div [symmetric]) (auto simp add: field_simps)
    ultimately show ?thesis by auto
  qed
  finally have "║1 / (2*\<pi>*\<i>) * ~\<integral> path (\<lambda>s. f s * a ᣔ s / s)║ \<le> 1 / (2*\<pi>) * 4 * B * a ᣔ b * ln (1 + T / b)"
    by (simp add: norm_divide norm_mult field_simps)
  also have "\<dots> \<le> 1 * B * a ᣔ b * ln (1 + T / b)"
  proof -
    have "1 / (2*\<pi>) * 4 \<le> 1" using pi_gt3 by auto
    thus ?thesis by (intro mult_right_mono) (use hT Hb hB in auto)
  qed
  finally show ?thesis unfolding path_def by auto
qed

definition has_subsum where "has_subsum f S x \<equiv> (\<lambda>n. if n \<in> S then f n else 0) sums x"
definition subsum where "subsum f S \<equiv> \<Sum>n. if n \<in> S then f n else 0"
definition subsummable (infix "subsummable" 50)
  where "f subsummable S \<equiv> summable (\<lambda>n. if n \<in> S then f n else 0)"

syntax "_subsum" :: "pttrn \<Rightarrow> \<nat> set \<Rightarrow> 'a \<Rightarrow> 'a"
  ("(2\<Sum>`_ \<in> (_)./ _)" [0, 0, 10] 10)
translations
  "\<Sum>` x\<in>S. t" => "CONST subsum (\<lambda>x. t) S"

syntax "_subsum_prop" :: "pttrn \<Rightarrow> bool \<Rightarrow> 'a \<Rightarrow> 'a"
  ("(2\<Sum>`_ | (_)./ _)" [0, 0, 10] 10)
translations
  "\<Sum>` x|P. t" => "CONST subsum (\<lambda>x. t) {x. P}"

syntax "_subsum_ge" :: "pttrn \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a"
  ("(2\<Sum>`_ \<ge> _./ _)" [0, 0, 10] 10)
translations
  "\<Sum>` x\<ge>n. t" => "CONST subsum (\<lambda>x. t) {n..}"

theorem has_subsum_finite:
  "finite F \<Longrightarrow> has_subsum f F (sum f F)"
  unfolding has_subsum_def by (rule sums_If_finite_set)

theorem has_subsum_If_finite_set:
  assumes "finite F"
  shows "has_subsum (\<lambda>n. if n \<in> F then f n else 0) A (sum f (F \<inter> A))"
proof -
  have "F \<inter> A = {x. x \<in> A \<and> x \<in> F}" by auto
  thus ?thesis unfolding has_subsum_def using assms
    by (auto simp add: if_if_eq_conj intro!: sums_If_finite)
qed

theorem has_subsum_If_finite:
  assumes "finite {n \<in> A. p n}"
  shows "has_subsum (\<lambda>n. if p n then f n else 0) A (sum f {n \<in> A. p n})"
unfolding has_subsum_def using assms
  by (auto simp add: if_if_eq_conj intro!: sums_If_finite)

theorem has_subsum_univ:
  "f sums v \<Longrightarrow> has_subsum f UNIV v" 
  unfolding has_subsum_def by auto

theorem subsumI:
  fixes f :: "\<nat> \<Rightarrow> 'a :: {t2_space, comm_monoid_add}"
  shows "has_subsum f A x \<Longrightarrow> x = subsum f A"
  unfolding has_subsum_def subsum_def by (intro sums_unique)

theorem has_subsum_summable:
  "has_subsum f A x \<Longrightarrow> f subsummable A"
  unfolding has_subsum_def subsummable_def by (rule sums_summable)

theorem subsummable_sums:
  fixes f :: "\<nat> \<Rightarrow> 'a :: {comm_monoid_add, t2_space}"
  shows "f subsummable S \<Longrightarrow> has_subsum f S (subsum f S)"
  unfolding subsummable_def has_subsum_def subsum_def by (intro summable_sums)

theorem has_subsum_diff_finite:
  fixes S :: "'a :: {topological_ab_group_add, t2_space}"
  assumes "finite F" "has_subsum f A S" "F \<subseteq> A"
  shows "has_subsum f (A - F) (S - sum f F)"
proof -
  define p where "p n \<equiv> if n \<in> F then 0 else (if n \<in> A then f n else 0)" for n
  define q where "q n \<equiv> if n \<in> A - F then f n else 0" for n
  have "F \<inter> A = F" using assms(3) by auto
  hence "p sums (S - sum f F)"
    using assms unfolding p_def has_subsum_def
    by (rule_tac sums_If_finite_set' [where ?S = S])
       (auto simp add: sum_negf sum.inter_restrict [symmetric])
  moreover have "p = q" unfolding p_def q_def by auto
  finally show ?thesis unfolding q_def has_subsum_def by auto
qed

theorem subsum_split:
  fixes f :: "\<nat> \<Rightarrow> 'a :: {topological_ab_group_add, t2_space}"
  assumes "f subsummable A" "finite F" "F \<subseteq> A"
  shows "subsum f A = sum f F + subsum f (A - F)"
proof -
  from assms(1) have "has_subsum f A (subsum f A)" by (intro subsummable_sums)
  hence "has_subsum f (A - F) (subsum f A - sum f F)"
    using assms by (intro has_subsum_diff_finite)
  hence "subsum f A - sum f F = subsum f (A - F)" by (rule subsumI)
  thus ?thesis by (auto simp add: algebra_simps)
qed

theorem has_subsum_zero [simp]: "has_subsum (\<lambda>n. 0) A 0" unfolding has_subsum_def by auto
theorem zero_subsummable [simp]: "(\<lambda>n. 0) subsummable A" unfolding subsummable_def by auto
theorem zero_subsum [simp]: "(\<Sum>`n\<in>A. 0 :: 'a :: {comm_monoid_add, t2_space}) = 0" unfolding subsum_def by auto

theorem has_subsum_minus:
  fixes f :: "\<nat> \<Rightarrow> 'a :: real_normed_vector"
  assumes "has_subsum f A a" "has_subsum g A b"
  shows "has_subsum (\<lambda>n. f n - g n) A (a - b)"
proof -
  define p where "p n = (if n \<in> A then f n else 0)" for n
  define q where "q n = (if n \<in> A then g n else 0)" for n
  have "(\<lambda>n. p n - q n) sums (a - b)"
    using assms unfolding p_def q_def has_subsum_def by (intro sums_diff)
  moreover have "(if n \<in> A then f n - g n else 0) = p n - q n" for n
    unfolding p_def q_def by auto
  ultimately show ?thesis unfolding has_subsum_def by auto
qed

theorem subsum_minus:
  assumes "f subsummable A" "g subsummable A"
  shows "subsum f A - subsum g A = (\<Sum>`n\<in>A. f n - g n :: 'a :: real_normed_vector)"
  by (intro subsumI has_subsum_minus subsummable_sums assms)

theorem subsummable_minus:
  assumes "f subsummable A" "g subsummable A"
  shows "(\<lambda>n. f n - g n :: 'a :: real_normed_vector) subsummable A"
  by (auto intro: has_subsum_summable has_subsum_minus subsummable_sums assms)

theorem has_subsum_uminus:
  assumes "has_subsum f A a"
  shows "has_subsum (\<lambda>n. - f n :: 'a :: real_normed_vector) A (- a)"
proof -
  have "has_subsum (\<lambda>n. 0 - f n) A (0 - a)"
    by (intro has_subsum_minus) (use assms in auto)
  thus ?thesis by auto
qed

theorem subsum_uminus:
  "f subsummable A \<Longrightarrow> - subsum f A = (\<Sum>`n\<in>A. - f n :: 'a :: real_normed_vector)"
  by (intro subsumI has_subsum_uminus subsummable_sums)

theorem subsummable_uminus:
  "f subsummable A \<Longrightarrow> (\<lambda>n. - f n :: 'a :: real_normed_vector) subsummable A"
  by (auto intro: has_subsum_summable has_subsum_uminus subsummable_sums)

theorem has_subsum_add:
  fixes f :: "\<nat> \<Rightarrow> 'a :: real_normed_vector"
  assumes "has_subsum f A a" "has_subsum g A b"
  shows "has_subsum (\<lambda>n. f n + g n) A (a + b)"
proof -
  have "has_subsum (\<lambda>n. f n - - g n) A (a - - b)"
    by (intro has_subsum_minus has_subsum_uminus assms)
  thus ?thesis by auto
qed

theorem subsum_add:
  assumes "f subsummable A" "g subsummable A"
  shows "subsum f A + subsum g A = (\<Sum>`n\<in>A. f n + g n :: 'a :: real_normed_vector)"
  by (intro subsumI has_subsum_add subsummable_sums assms)

theorem subsummable_add:
  assumes "f subsummable A" "g subsummable A"
  shows "(\<lambda>n. f n + g n :: 'a :: real_normed_vector) subsummable A"
  by (auto intro: has_subsum_summable has_subsum_add subsummable_sums assms)

theorem subsum_cong:
  "(\<And>x. x \<in> A \<Longrightarrow> f x = g x) \<Longrightarrow> subsum f A = subsum g A"
  unfolding subsum_def by (intro suminf_cong) auto

theorem subsummable_cong:
  fixes f :: "\<nat> \<Rightarrow> 'a :: real_normed_vector"
  shows "(\<And>x. x \<in> A \<Longrightarrow> f x = g x) \<Longrightarrow> (f subsummable A) = (g subsummable A)"
  unfolding subsummable_def by (intro summable_cong) auto

theorem subsum_norm_bound:
  fixes f :: "\<nat> \<Rightarrow> 'a :: banach"
  assumes "g subsummable A" "\<And>n. n \<in> A \<Longrightarrow> ║f n║ \<le> g n"
  shows "║subsum f A║ \<le> subsum g A"
  using assms unfolding subsummable_def subsum_def
  by (intro suminf_norm_bound) auto

theorem eval_fds_subsum:
  fixes f :: "'a :: {nat_power, banach, real_normed_field} fds"
  assumes "fds_converges f s"
  shows "has_subsum (\<lambda>n. d\<^sub>n f n / nat_power n s) {1..} (eval_fds f s)"
proof -
  let ?f = "\<lambda>n. d\<^sub>n f n / nat_power n s"
  let ?v = "eval_fds f s"
  have "has_subsum (\<lambda>n. ?f n) UNIV ?v"
    by (intro has_subsum_univ fds_converges_iff [THEN iffD1] assms)
  hence "has_subsum ?f (UNIV - {0}) (?v - sum ?f {0})"
    by (intro has_subsum_diff_finite) auto
  moreover have "UNIV - {0 :: \<nat>} = {1..}" by auto
  ultimately show ?thesis by auto
qed

theorem fds_abs_subsummable:
  fixes f :: "'a :: {nat_power, banach, real_normed_field} fds"
  assumes "fds_abs_converges f s"
  shows "(\<lambda>n. ║d\<^sub>n f n / nat_power n s║) subsummable {1..}"
proof -
  have "summable (\<lambda>n. ║d\<^sub>n f n / nat_power n s║)"
    by (subst fds_abs_converges_def [symmetric]) (rule assms)
  moreover have "║d\<^sub>n f n / nat_power n s║ = 0" when "\<not> 1 \<le> n" for n
  proof -
    have "n = 0" using that by auto
    thus ?thesis by auto
  qed
  hence "(\<lambda>n. if 1 \<le> n then ║d\<^sub>n f n / nat_power n s║ else 0)
       = (\<lambda>n. ║d\<^sub>n f n / nat_power n s║)" by auto
  ultimately show ?thesis unfolding subsummable_def by auto
qed

theorem subsum_mult2:
  fixes f :: "\<nat> \<Rightarrow> 'a :: real_normed_algebra"
  shows "f subsummable A \<Longrightarrow> (\<Sum>`x\<in>A. f x * c) = subsum f A * c"
unfolding subsum_def subsummable_def
  by (subst suminf_mult2) (auto intro: suminf_cong)

theorem subsummable_mult2:
  fixes f :: "\<nat> \<Rightarrow> 'a :: real_normed_algebra"
  assumes "f subsummable A"
  shows "(\<lambda>x. f x * c) subsummable A"
proof -
  have "summable (\<lambda>n. (if n \<in> A then f n else 0) * c)" (is ?P)
    using assms unfolding subsummable_def by (intro summable_mult2)
  moreover have "?P = ?thesis"
    unfolding subsummable_def by (rule summable_cong) auto
  ultimately show ?thesis by auto
qed

theorem subsum_ge_limit:
  "lim (\<lambda>N. \<Sum>n = m..N. f n) = (\<Sum>`n \<ge> m. f n)"
proof -
  define g where "g n \<equiv> if n \<in> {m..} then f n else 0" for n
  have "(\<Sum>n. g n) = lim (\<lambda>N. \<Sum>n<N. g n)" by (rule suminf_eq_lim)
  also have "\<dots> = lim (\<lambda>N. \<Sum>n<N + 1. g n)"
    unfolding lim_def using LIMSEQ_ignore_initial_segment LIMSEQ_offset
    by (intro The_cong iffI) blast
  also have "\<dots> = lim (\<lambda>N. \<Sum>n = m..N. f n)"
  proof -
    have "{x. x < N + 1 \<and> m \<le> x} = {m..N}" for N by auto
    thus ?thesis unfolding g_def by (subst sum.inter_filter [symmetric]) auto
  qed
  finally show ?thesis unfolding subsum_def g_def by auto
qed

theorem has_subsum_ge_limit:
  fixes f :: "\<nat> \<Rightarrow> 'a :: {t2_space, comm_monoid_add, topological_space}"
  assumes "((\<lambda>N. \<Sum>n = m..N. f n) \<longlongrightarrow> l) +\<infinity>"
  shows "has_subsum f {m..} l"
proof -
  define g where "g n \<equiv> if n \<in> {m..} then f n else 0" for n
  have "((\<lambda>N. \<Sum>n<N + 1. g n) \<longlongrightarrow> l) +\<infinity>"
  proof -
    have "{x. x < N + 1 \<and> m \<le> x} = {m..N}" for N by auto
    with assms show ?thesis
      unfolding g_def by (subst sum.inter_filter [symmetric]) auto
  qed
  hence "((\<lambda>N. \<Sum>n<N. g n) \<longlongrightarrow> l) +\<infinity>" by (rule_tac LIMSEQ_offset)
  thus ?thesis unfolding has_subsum_def sums_def g_def by auto
qed

theorem eval_fds_complex:
  fixes f :: "\<complex> fds"
  assumes "fds_converges f s"
  shows "has_subsum (\<lambda>n. d\<^sub>n f n / n \<nat>ᣔ s) {1..} (eval_fds f s)"
proof -
  have "has_subsum (\<lambda>n. d\<^sub>n f n / nat_power n s) {1..} (eval_fds f s)"
    by (intro eval_fds_subsum assms)
  thus ?thesis unfolding nat_power_complex_def .
qed

theorem eval_fds_complex_subsum:
  fixes f :: "\<complex> fds"
  assumes "fds_converges f s"
  shows "eval_fds f s = (\<Sum>`n \<ge> 1. d\<^sub>n f n / n \<nat>ᣔ s)"
        "(\<lambda>n. d\<^sub>n f n / n \<nat>ᣔ s) subsummable {1..}"
proof (goal_cases)
  case 1 show ?case by (intro subsumI eval_fds_complex assms)
  case 2 show ?case by (intro has_subsum_summable) (rule eval_fds_complex assms)+
qed

theorem nat_lt_real_iff:
  "(n :: \<nat>) < (a :: \<real>) = (n < nat \<lceil>a\<rceil>)"
proof -
  have "n < a = (of_int n < a)" by auto
  also have "\<dots> = (n < \<lceil>a\<rceil>)" by (rule less_ceiling_iff [symmetric])
  also have "\<dots> = (n < nat \<lceil>a\<rceil>)" by auto
  finally show ?thesis .
qed

theorem nat_le_real_iff:
  "(n :: \<nat>) \<le> (a :: \<real>) = (n < nat (\<lfloor>a\<rfloor> + 1))"
proof -
  have "n \<le> a = (of_int n \<le> a)" by auto
  also have "\<dots> = (n \<le> \<lfloor>a\<rfloor>)" by (rule le_floor_iff [symmetric])
  also have "\<dots> = (n < \<lfloor>a\<rfloor> + 1)" by auto
  also have "\<dots> = (n < nat (\<lfloor>a\<rfloor> + 1))" by auto
  finally show ?thesis .
qed

locale perron_locale =
  fixes b B H T x :: \<real> and f :: "\<complex> fds"
  assumes Hb: "0 < b" and hT: "b \<le> T"
    and Hb': "abs_conv_abscissa f < b"
    and hH: "2 \<le> H" and hH': "b + 1 \<le> H" and Hx: "2 \<le> x"
    and hB: "(\<Sum>`n \<ge> 1. ║d\<^sub>n f n║ / n \<nat>ᣔ b) \<le> B"
begin
definition r where "r a \<equiv>
  if a \<noteq> 1 then min (1 / (2 * T * \<bar>ln a\<bar>)) (2 + ln (T / b))
  else (2 + ln (T / b))"
definition path where "path \<equiv> linepath (\<complex> b (-T)) (\<complex> b T)"
definition img_path where "img_path \<equiv> path_image path"
definition \<sigma>\<^sub>a where "\<sigma>\<^sub>a \<equiv> abs_conv_abscissa f"
definition region where "region = {n :: \<nat>. x - x / H \<le> n \<and> n \<le> x + x / H}"
definition F where "F (a :: \<real>) \<equiv>
  1 / (2*\<pi>*\<i>) * ~\<integral> path (\<lambda>s. a ᣔ s / s) - (if 1 \<le> a then 1 else 0)"
definition F' where "F' (n :: \<nat>) \<equiv> F (x / n)"

lemma hT': "0 < T" using Hb hT by auto
lemma cond: "0 < b" "b \<le> T" "0 < T" using Hb hT hT' by auto

theorem perron_integrable:
  assumes "(0 :: \<real>) < a"
  shows "(\<lambda>s. a ᣔ s / s) \<llangle>~\<integral>\<rrangle> (linepath (\<complex> b (-T)) (\<complex> b T))"
using cond assms
by (intro contour_integrable_continuous_linepath continuous_intros)
   (auto simp add: closed_segment_def legacy_Complex_simps field_simps)

theorem perron_aux_1:
  assumes Ha: "1 < a"
  shows "║F a║ \<le> 1 / 2 * a ᣔ b / (T * \<bar>ln a\<bar>)"
proof -
  define f where "f \<equiv> \<lambda>s :: \<complex>. a ᣔ s / s"
  define U where "U \<equiv> 2 * T\<^sup>2 * \<bar>ln a\<bar>"
  have hU: "0 < U" unfolding U_def using cond assms by auto
  note assms' = cond assms this
  define P\<^sub>1 where "P\<^sub>1 \<equiv> linepath (\<complex> (-U) (-T)) (\<complex> b (-T))"
  define P\<^sub>2 where "P\<^sub>2 \<equiv> linepath (\<complex> b (-T)) (\<complex> b T)"
  define P\<^sub>3 where "P\<^sub>3 \<equiv> linepath (\<complex> b T) (\<complex> (-U) T)"
  define P\<^sub>4 where "P\<^sub>4 \<equiv> linepath (\<complex> (-U) T) (\<complex> (-U) (-T))"
  define P where "P \<equiv> P\<^sub>1 +++ P\<^sub>2 +++ P\<^sub>3 +++ P\<^sub>4"
  define I\<^sub>1 I\<^sub>2 I\<^sub>3 I\<^sub>4 where
    "I\<^sub>1 \<equiv> ~\<integral> P\<^sub>1 f" and "I\<^sub>2 \<equiv> ~\<integral> P\<^sub>2 f" and
    "I\<^sub>3 \<equiv> ~\<integral> P\<^sub>3 f" and "I\<^sub>4 \<equiv> ~\<integral> P\<^sub>4 f"
  define rpath where "rpath \<equiv> rectpath (\<complex> (-U) (-T)) (\<complex> b T)"
  note P_defs = P_def P\<^sub>1_def P\<^sub>2_def P\<^sub>3_def P\<^sub>4_def
  note I_defs = I\<^sub>1_def I\<^sub>2_def I\<^sub>3_def I\<^sub>4_def
  have 1: "\<And>A B x. A \<subseteq> B \<Longrightarrow> x \<notin> A \<Longrightarrow> A \<subseteq> B - {x}" by auto
  have "path_image (rectpath (\<complex> (- U) (- T)) (\<complex> b T)) \<subseteq> cbox (\<complex> (- U) (- T)) (\<complex> b T) - {0}"
    using assms'
    by (intro 1 path_image_rectpath_subset_cbox)
       (auto simp add: path_image_rectpath)
  moreover have "0 \<in> box (\<complex> (- U) (- T)) (\<complex> b T)"
    using assms' by (simp add: mem_box Basis_complex_def)
  ultimately have
    "((\<lambda>s. a ᣔ s / (s - 0)) #~\<integral> 2*\<pi>*\<i> * winding_number rpath 0 * a ᣔ (0 :: \<complex>)) rpath"
    "winding_number rpath 0 = 1"
    unfolding rpath_def
    by (intro Cauchy_integral_formula_convex_simple
              [where S = "cbox (\<complex> (-U) (-T)) (\<complex> b T)"])
       (auto intro!: assms' holomorphic_on_powr_right winding_number_rectpath
             simp add: mem_box Basis_complex_def)
  hence "(f #~\<integral> 2*\<pi>*\<i>) rpath" unfolding f_def using Ha by auto
  hence 2: "(f #~\<integral> 2*\<pi>*\<i>) P"
    unfolding rpath_def P_defs rectpath_def Let_def by simp
  hence "f \<llangle>~\<integral>\<rrangle> P" by (intro has_contour_integral_integrable) (use 2 in auto)
  hence 3: "f \<llangle>~\<integral>\<rrangle> P\<^sub>1" "f \<llangle>~\<integral>\<rrangle> P\<^sub>2" "f \<llangle>~\<integral>\<rrangle> P\<^sub>3" "f \<llangle>~\<integral>\<rrangle> P\<^sub>4" unfolding P_defs by auto
  from 2 have "I\<^sub>1 + I\<^sub>2 + I\<^sub>3 + I\<^sub>4 = 2*\<pi>*\<i>" unfolding P_defs I_defs by (rule has_chain_integral_chain_integral4)
  hence "I\<^sub>2 - 2*\<pi>*\<i> = - (I\<^sub>1 + I\<^sub>3 + I\<^sub>4)" by (simp add: field_simps)
  hence "║I\<^sub>2 - 2*\<pi>*\<i>║ = ║- (I\<^sub>1 + I\<^sub>3 + I\<^sub>4)║" by auto
  also have "\<dots> = ║I\<^sub>1 + I\<^sub>3 + I\<^sub>4║" by (rule norm_minus_cancel)
  also have "\<dots> \<le> ║I\<^sub>1 + I\<^sub>3║ + ║I\<^sub>4║" by (rule norm_triangle_ineq)
  also have "\<dots> \<le> ║I\<^sub>1║ + ║I\<^sub>3║ + ║I\<^sub>4║" using norm_triangle_ineq by auto
  finally have *: "║I\<^sub>2 - 2*\<pi>*\<i>║ \<le> ║I\<^sub>1║ + ║I\<^sub>3║ + ║I\<^sub>4║" .
  have I\<^sub>2_val: "║I\<^sub>2 / (2*\<pi>*\<i>) - 1║ \<le> 1 / (2*\<pi>) * (║I\<^sub>1║ + ║I\<^sub>3║ + ║I\<^sub>4║)"
  proof -
    have "I\<^sub>2 - 2*\<pi>*\<i> = (I\<^sub>2 / (2*\<pi>*\<i>) - 1) * (2*\<pi>*\<i>)" by (auto simp add: field_simps)
    hence "║I\<^sub>2 - 2*\<pi>*\<i>║ = ║(I\<^sub>2 / (2*\<pi>*\<i>) - 1) * (2*\<pi>*\<i>)║" by auto
    also have "\<dots> = ║I\<^sub>2 / (2*\<pi>*\<i>) - 1║ * (2*\<pi>)" by (auto simp add: norm_mult)
    finally have "║I\<^sub>2 / (2*\<pi>*\<i>) - 1║ = 1 / (2*\<pi>) * ║I\<^sub>2 - 2*\<pi>*\<i>║" by auto
    also have "\<dots> \<le> 1 / (2*\<pi>) * (║I\<^sub>1║ + ║I\<^sub>3║ + ║I\<^sub>4║)"
      using * by (subst mult_le_cancel_left_pos) auto
    finally show ?thesis .
  qed
  define Q where "Q t \<equiv> linepath (\<complex> (-U) t) (\<complex> b t)" for t
  define g where "g t \<equiv> ~\<integral> (Q t) f" for t
  have Q_1: "(f #~\<integral> I\<^sub>1) (Q (-T))"
    using 3(1) unfolding P\<^sub>1_def I\<^sub>1_def Q_def
    by (rule has_contour_integral_integral)
  have Q_2: "(f #~\<integral> -I\<^sub>3) (Q T)"
    using 3(3) unfolding P\<^sub>3_def I\<^sub>3_def Q_def
    by (subst contour_integral_reversepath [symmetric],
        auto intro!: has_contour_integral_integral)
       (subst contour_integrable_reversepath_eq [symmetric], auto)
  have subst_I\<^sub>1_I\<^sub>3: "I\<^sub>1 = g (- T)" "I\<^sub>3 = - g T"
    using Q_1 Q_2 unfolding g_def by (auto simp add: contour_integral_unique)
  have g_bound: "║g t║ \<le> a ᣔ b / (T * \<bar>ln a\<bar>)"
    when Ht: "\<bar>t\<bar> = T" for t
  proof -
    have "(f #~\<integral> g t) (Q t)" proof -
      consider "t = T" | "t = -T" using Ht by fastforce
      hence "f \<llangle>~\<integral>\<rrangle> Q t" using Q_1 Q_2 by (metis has_contour_integral_integrable)
      thus ?thesis unfolding g_def by (rule has_contour_integral_integral)
    qed
    hence "((\<lambda>x. a ᣔ (x + Im (\<complex> (-U) t) * \<i>) / (x + Im (\<complex> (-U) t) * \<i>)) #\<integral> (g t))
          {Re (\<complex> (-U) t) .. Re (\<complex> b t)}"
      unfolding Q_def f_def
      by (subst has_contour_integral_linepath_same_Im_iff [symmetric])
         (use hU Hb in auto)
    hence *: "((\<lambda>x. a ᣔ (x + t * \<i>) / (x + t * \<i>)) #\<integral> g t) {-U..b}" by auto
    hence "║g t║ = ║\<integral> {-U..b} (\<lambda>x. a ᣔ (x + t * \<i>) / (x + t * \<i>))║" by (auto simp add: integral_unique)
    also have "\<dots> \<le> \<integral> {-U..b} (\<lambda>x. a ᣔ x / T)"
    proof (rule integral_norm_bound_integral)
      show "(\<lambda>x. a ᣔ (x + t * \<i>) / (x + t * \<i>)) \<llangle>\<integral>\<rrangle> {-U..b}" using * by auto
      have "(\<lambda>x. a ᣔ x / (of_real T)) \<llangle>\<integral>\<rrangle> {-U..b}"
        by (intro integrable_on_cdivide powr_integrable) (use hU Ha Hb in auto)
      thus "(\<lambda>x. a ᣔ x / T) \<llangle>\<integral>\<rrangle> {-U..b}" by auto
    next
      fix x assume "x \<in> {-U..b}"
      have "║a ᣔ (x + t * \<i>)║ = Re a ᣔ Re (x + t * \<i>)" by (rule norm_powr_real_powr) (use Ha in auto)
      also have "\<dots> = a ᣔ x" by auto
      finally have *: "║a ᣔ (x + t * \<i>)║ = a ᣔ x" .
      have "T = \<bar>Im (x + t * \<i>)\<bar>" using Ht by auto
      also have "\<dots> \<le> ║x + t * \<i>║" by (rule abs_Im_le_cmod)
      finally have "T \<le> ║x + t * \<i>║" .
      with * show "║a ᣔ (x + t * \<i>) / (x + t * \<i>)║ \<le> a ᣔ x / T"
        by (subst norm_divide) (rule frac_le, use assms' in auto)
    qed
    also have "\<dots> = \<integral> {-U..b} (\<lambda>x. a ᣔ x) / T" by auto
    also have "\<dots> \<le> a ᣔ b / (T * \<bar>ln a\<bar>)"
    proof -
      have "\<integral> {-U..b} (\<lambda>x. a ᣔ x) \<le> a ᣔ b / \<bar>ln a\<bar>"
        by (rule powr_integral_bound_gt_1) (use hU Ha Hb in auto)
      thus ?thesis using hT' by (auto simp add: field_simps)
    qed
    finally show ?thesis .
  qed
  have "║I\<^sub>4║ \<le> a ᣔ -U / U * ║\<complex> (- U) (- T) - \<complex> (- U) T║"
  proof -
    have "f \<llangle>~\<integral>\<rrangle> P\<^sub>4" by (rule 3)
    moreover have "0 \<le> a ᣔ - U / U" using hU by auto
    moreover have "║f z║ \<le> a ᣔ - U / U"
      when *: "z \<in> closed_segment (\<complex> (- U) T) (\<complex> (- U) (- T))" for z
    proof -
      from * have Re_z: "Re z = - U"
        unfolding closed_segment_def
        by (auto simp add: legacy_Complex_simps field_simps)
      hence "U = \<bar>Re z\<bar>" using hU by auto
      also have "\<dots> \<le> ║z║" by (rule abs_Re_le_cmod)
      finally have zmod: "U \<le> ║z║" .
      have "║f z║ = ║a ᣔ z║ / ║z║" unfolding f_def by (rule norm_divide)
      also have "\<dots> \<le> a ᣔ - U / U"
        by (subst norm_powr_real_powr, use Ha in auto)
           (rule frac_le, use hU Re_z zmod in auto)
      finally show ?thesis .
    qed
    ultimately show ?thesis unfolding I\<^sub>4_def P\<^sub>4_def by (rule contour_integral_bound_linepath)
  qed
  also have "\<dots> = a ᣔ -U / (2 * T\<^sup>2 * \<bar>ln a\<bar>) * \<surd> ((2 * T)\<^sup>2)"
    unfolding U_def by (simp add: legacy_Complex_simps)
  also have "\<dots> = a ᣔ -U / (T * \<bar>ln a\<bar>)"
  proof -
    have "\<surd> ((2 * T)\<^sup>2) = \<bar>2 * T\<bar>" by (rule real_sqrt_abs)
    thus ?thesis using hT' unfolding power2_eq_square by (auto simp add: field_simps)
  qed
  also have "\<dots> \<le> a ᣔ b / (T * \<bar>ln a\<bar>)"
    using hU Ha Hb hT by (auto simp add: field_simps)
  finally have I\<^sub>4_bound: "║I\<^sub>4║ \<le> a ᣔ b / (T * \<bar>ln a\<bar>)" .
  hence "║I\<^sub>2 / (2*\<pi>*\<i>) - 1║ \<le> 1 / (2*\<pi>) * (║g (- T)║ + ║- g T║ + ║I\<^sub>4║)"
    using I\<^sub>2_val subst_I\<^sub>1_I\<^sub>3 by auto
  also have "\<dots> \<le> 3 / (2*\<pi>) * (a ᣔ b / (T * \<bar>ln a\<bar>))"
  proof -
    have "║g T║ \<le> a ᣔ b / (T * \<bar>ln a\<bar>)"
         "║g (- T)║ \<le> a ᣔ b / (T * \<bar>ln a\<bar>)"
      using hT' by (auto intro: g_bound)
    hence "║g (- T)║ + ║- g T║ + ║I\<^sub>4║ \<le> 3 * a ᣔ b / (T * \<bar>ln a\<bar>)"
      using I\<^sub>4_bound by auto
    thus ?thesis using pi_gt_zero pi_gt3 by (auto simp add: field_simps)
  qed
  also have "\<dots> \<le> 1 / 2 * (a ᣔ b / (T * \<bar>ln a\<bar>))"
  proof -
    have "3 / (2*\<pi>) \<le> 1 / 2" using pi_gt3 by auto
    moreover have "a ᣔ b / (T * \<bar>ln a\<bar>) \<ge> 0" using hT' by auto
    ultimately show ?thesis by (intro mult_right_mono)
  qed
  finally show ?thesis
    using Ha unfolding I\<^sub>2_def P\<^sub>2_def f_def F_def path_def by auto
qed

theorem perron_aux_2:
  assumes Ha: "0 < a \<and> a < 1"
  shows "║F a║ \<le> 1 / 2 * a ᣔ b / (T * \<bar>ln a\<bar>)"
proof -
  define f where "f \<equiv> \<lambda>s :: \<complex>. a ᣔ s / s"
  define U where "U \<equiv> max (b + 1) (2 * T\<^sup>2 * \<bar>ln a\<bar>)"
  have hU: "0 < U" unfolding U_def using Hb by auto
  have bU: "b < U" unfolding U_def by auto
  note assms' = cond assms hU bU
  define P\<^sub>1 where "P\<^sub>1 \<equiv> linepath (\<complex> b (-T)) (\<complex> U (-T))"
  define P\<^sub>2 where "P\<^sub>2 \<equiv> linepath (\<complex> U (-T)) (\<complex> U T)"
  define P\<^sub>3 where "P\<^sub>3 \<equiv> linepath (\<complex> U T) (\<complex> b T)"
  define P\<^sub>4 where "P\<^sub>4 \<equiv> linepath (\<complex> b T) (\<complex> b (-T))"
  define P where "P \<equiv> P\<^sub>1 +++ P\<^sub>2 +++ P\<^sub>3 +++ P\<^sub>4"
  define I\<^sub>1 I\<^sub>2 I\<^sub>3 I\<^sub>4 where
    "I\<^sub>1 \<equiv> ~\<integral> P\<^sub>1 f" and "I\<^sub>2 \<equiv> ~\<integral> P\<^sub>2 f" and
    "I\<^sub>3 \<equiv> ~\<integral> P\<^sub>3 f" and "I\<^sub>4 \<equiv> ~\<integral> P\<^sub>4 f"
  define rpath where "rpath \<equiv> rectpath (\<complex> b (- T)) (\<complex> U T)"
  note P_defs = P_def P\<^sub>1_def P\<^sub>2_def P\<^sub>3_def P\<^sub>4_def
  note I_defs = I\<^sub>1_def I\<^sub>2_def I\<^sub>3_def I\<^sub>4_def
  have "path_image (rectpath (\<complex> b (- T)) (\<complex> U T)) \<subseteq> cbox (\<complex> b (- T)) (\<complex> U T)"
    by (intro path_image_rectpath_subset_cbox) (use assms' in auto)
  moreover have "0 \<notin> cbox (\<complex> b (- T)) (\<complex> U T)"
    using Hb unfolding cbox_def by (auto simp add: Basis_complex_def)
  ultimately have "((\<lambda>s. a ᣔ s / (s - 0)) #~\<integral> 0) rpath"
    unfolding rpath_def
    by (intro Cauchy_theorem_convex_simple
              [where S = "cbox (\<complex> b (- T)) (\<complex> U T)"])
       (auto intro!: holomorphic_on_powr_right holomorphic_on_divide)
  hence "(f #~\<integral> 0) rpath" unfolding f_def using Ha by auto
  hence 1: "(f #~\<integral> 0) P" unfolding rpath_def P_defs rectpath_def Let_def by simp
  hence "f \<llangle>~\<integral>\<rrangle> P" by (intro has_contour_integral_integrable) (use 1 in auto)
  hence 2: "f \<llangle>~\<integral>\<rrangle> P\<^sub>1" "f \<llangle>~\<integral>\<rrangle> P\<^sub>2" "f \<llangle>~\<integral>\<rrangle> P\<^sub>3" "f \<llangle>~\<integral>\<rrangle> P\<^sub>4" unfolding P_defs by auto
  from 1 have "I\<^sub>1 + I\<^sub>2 + I\<^sub>3 + I\<^sub>4 = 0" unfolding P_defs I_defs by (rule has_chain_integral_chain_integral4)
  hence "I\<^sub>4 = - (I\<^sub>1 + I\<^sub>2 + I\<^sub>3)" by (metis neg_eq_iff_add_eq_0)
  hence "║I\<^sub>4║ = ║- (I\<^sub>1 + I\<^sub>2 + I\<^sub>3)║" by auto
  also have "\<dots> = ║I\<^sub>1 + I\<^sub>2 + I\<^sub>3║" by (rule norm_minus_cancel)
  also have "\<dots> \<le> ║I\<^sub>1 + I\<^sub>2║ + ║I\<^sub>3║" by (rule norm_triangle_ineq)
  also have "\<dots> \<le> ║I\<^sub>1║ + ║I\<^sub>2║ + ║I\<^sub>3║" using norm_triangle_ineq by auto
  finally have "║I\<^sub>4║ \<le> ║I\<^sub>1║ + ║I\<^sub>2║ + ║I\<^sub>3║" .
  hence I\<^sub>4_val: "║I\<^sub>4 / (2*\<pi>*\<i>)║ \<le> 1 / (2*\<pi>) * (║I\<^sub>1║ + ║I\<^sub>2║ + ║I\<^sub>3║)"
    by (auto simp add: norm_divide norm_mult field_simps)
  define Q where "Q t \<equiv> linepath (\<complex> b t) (\<complex> U t)" for t
  define g where "g t \<equiv> ~\<integral> (Q t) f" for t
  have Q_1: "(f #~\<integral> I\<^sub>1) (Q (-T))"
    using 2(1) unfolding P\<^sub>1_def I\<^sub>1_def Q_def
    by (rule has_contour_integral_integral)
  have Q_2: "(f #~\<integral> -I\<^sub>3) (Q T)"
    using 2(3) unfolding P\<^sub>3_def I\<^sub>3_def Q_def
    by (subst contour_integral_reversepath [symmetric],
        auto intro!: has_contour_integral_integral)
       (subst contour_integrable_reversepath_eq [symmetric], auto)
  have subst_I\<^sub>1_I\<^sub>3: "I\<^sub>1 = g (- T)" "I\<^sub>3 = - g T"
    using Q_1 Q_2 unfolding g_def by (auto simp add: contour_integral_unique)
  have g_bound: "║g t║ \<le> a ᣔ b / (T * \<bar>ln a\<bar>)"
    when Ht: "\<bar>t\<bar> = T" for t
  proof -
    have "(f #~\<integral> g t) (Q t)" proof -
      consider "t = T" | "t = -T" using Ht by fastforce
      hence "f \<llangle>~\<integral>\<rrangle> Q t" using Q_1 Q_2 by (metis has_contour_integral_integrable)
      thus ?thesis unfolding g_def by (rule has_contour_integral_integral)
    qed
    hence "((\<lambda>x. a ᣔ (x + Im (\<complex> b t) * \<i>) / (x + Im (\<complex> b t) * \<i>)) #\<integral> (g t))
          {Re (\<complex> b t) .. Re (\<complex> U t)}"
      unfolding Q_def f_def
      by (subst has_contour_integral_linepath_same_Im_iff [symmetric])
         (use assms' in auto)
    hence *: "((\<lambda>x. a ᣔ (x + t * \<i>) / (x + t * \<i>)) #\<integral> g t) {b..U}" by auto
    hence "║g t║ = ║\<integral> {b..U} (\<lambda>x. a ᣔ (x + t * \<i>) / (x + t * \<i>))║" by (auto simp add: integral_unique)
    also have "\<dots> \<le> \<integral> {b..U} (\<lambda>x. a ᣔ x / T)"
    proof (rule integral_norm_bound_integral)
      show "(\<lambda>x. a ᣔ (x + t * \<i>) / (x + t * \<i>)) \<llangle>\<integral>\<rrangle> {b..U}" using * by auto
      have "(\<lambda>x. a ᣔ x / (of_real T)) \<llangle>\<integral>\<rrangle> {b..U}"
        by (intro integrable_on_cdivide powr_integrable) (use assms' in auto)
      thus "(\<lambda>x. a ᣔ x / T) \<llangle>\<integral>\<rrangle> {b..U}" by auto
    next
      fix x assume "x \<in> {b..U}"
      have "║a ᣔ (x + t * \<i>)║ = Re a ᣔ Re (x + t * \<i>)" by (rule norm_powr_real_powr) (use Ha in auto)
      also have "\<dots> = a ᣔ x" by auto
      finally have 1: "║a ᣔ (x + t * \<i>)║ = a ᣔ x" .
      have "T = \<bar>Im (x + t * \<i>)\<bar>" using Ht by auto
      also have "\<dots> \<le> ║x + t * \<i>║" by (rule abs_Im_le_cmod)
      finally have 2: "T \<le> ║x + t * \<i>║" .
      from 1 2 show "║a ᣔ (x + t * \<i>) / (x + t * \<i>)║ \<le> a ᣔ x / T"
        by (subst norm_divide) (rule frac_le, use hT' in auto)
    qed
    also have "\<dots> = \<integral> {b..U} (\<lambda>x. a ᣔ x) / T" by auto
    also have "\<dots> \<le> a ᣔ b / (T * \<bar>ln a\<bar>)"
    proof -
      have "\<integral> {b..U} (\<lambda>x. a ᣔ x) \<le> a ᣔ b / \<bar>ln a\<bar>"
        by (rule powr_integral_bound_lt_1) (use assms' in auto)
      thus ?thesis using hT' by (auto simp add: field_simps)
    qed
    finally show ?thesis .
  qed
  have "║I\<^sub>2║ \<le> a ᣔ U / U * ║\<complex> U T - \<complex> U (- T)║"
  proof -
    have "f \<llangle>~\<integral>\<rrangle> P\<^sub>2" by (rule 2)
    moreover have "0 \<le> a ᣔ U / U" using hU by auto
    moreover have "║f z║ \<le> a ᣔ U / U"
      when *: "z \<in> closed_segment (\<complex> U (- T)) (\<complex> U T)" for z
    proof -
      from * have Re_z: "Re z = U"
        unfolding closed_segment_def
        by (auto simp add: legacy_Complex_simps field_simps)
      hence "U = \<bar>Re z\<bar>" using hU by auto
      also have "\<dots> \<le> ║z║" by (rule abs_Re_le_cmod)
      finally have zmod: "U \<le> ║z║" .
      have "║f z║ = ║a ᣔ z║ / ║z║" unfolding f_def by (rule norm_divide)
      also have "\<dots> \<le> a ᣔ U / U"
        by (subst norm_powr_real_powr, use Ha in auto)
           (rule frac_le, use hU Re_z zmod in auto)
      finally show ?thesis .
    qed
    ultimately show ?thesis unfolding I\<^sub>2_def P\<^sub>2_def by (rule contour_integral_bound_linepath)
  qed
  also have "\<dots> \<le> a ᣔ U / (2 * T\<^sup>2 * \<bar>ln a\<bar>) * \<surd> ((2 * T)\<^sup>2)"
  proof -
    have "2 * T\<^sup>2 * \<bar>ln a\<bar> \<le> U" unfolding U_def by auto
    moreover have "0 < U * (\<bar>ln a\<bar> * T\<^sup>2)"
      using assms' unfolding power2_eq_square by (smt (verit) mult_pos_pos ln_less_zero)
    ultimately show ?thesis
      by (simp add: legacy_Complex_simps) (rule divide_left_mono, auto)
  qed
  also have "\<dots> = a ᣔ U / (T * \<bar>ln a\<bar>)"
  proof -
    have "\<surd> ((2 * T)\<^sup>2) = \<bar>2 * T\<bar>" by (rule real_sqrt_abs)
    thus ?thesis using hT' unfolding power2_eq_square by (auto simp add: field_simps)
  qed
  also have "\<dots> \<le> a ᣔ b / (T * \<bar>ln a\<bar>)"
  proof -
    have "a ᣔ U \<le> a ᣔ b" using assms' by (subst powr_mono_lt_1_cancel) auto
    thus ?thesis using hT' by (intro divide_right_mono) auto
  qed
  finally have I\<^sub>2_bound: "║I\<^sub>2║ \<le> a ᣔ b / (T * \<bar>ln a\<bar>)" .
  hence "║I\<^sub>4 / (2*\<pi>*\<i>)║ \<le> 1 / (2*\<pi>) * (║g (- T)║ + ║I\<^sub>2║ + ║- g T║)"
    using I\<^sub>4_val subst_I\<^sub>1_I\<^sub>3 by auto
  also have "\<dots> \<le> 3 / (2*\<pi>) * (a ᣔ b / (T * \<bar>ln a\<bar>))"
  proof -
    have "║g T║ \<le> a ᣔ b / (T * \<bar>ln a\<bar>)"
         "║g (- T)║ \<le> a ᣔ b / (T * \<bar>ln a\<bar>)"
      using hT' by (auto intro: g_bound)
    hence "║g (- T)║ + ║- g T║ + ║I\<^sub>2║ \<le> 3 * a ᣔ b / (T * \<bar>ln a\<bar>)"
      using I\<^sub>2_bound by auto
    thus ?thesis using pi_gt_zero pi_gt3 by (auto simp add: field_simps)
  qed
  also have "\<dots> \<le> 1 / 2 * (a ᣔ b / (T * \<bar>ln a\<bar>))"
  proof -
    have "3 / (2*\<pi>) \<le> 1 / 2" using pi_gt3 by auto
    moreover have "a ᣔ b / (T * \<bar>ln a\<bar>) \<ge> 0" using hT' by auto
    ultimately show ?thesis by (intro mult_right_mono)
  qed
  finally have
    "║1 / (2*\<pi>*\<i>) * ~\<integral> (reversepath P\<^sub>4) f║ \<le> 1 / 2 * a ᣔ b / (T * \<bar>ln a\<bar>)"
    unfolding I\<^sub>4_def P\<^sub>4_def by (subst contour_integral_reversepath) auto
  thus ?thesis unfolding P\<^sub>4_def f_def F_def path_def using Ha by auto
qed

theorem perron_aux_3:
  assumes Ha: "0 < a"
  shows "║1 / (2*\<pi>*\<i>) * ~\<integral> path (\<lambda>s. a ᣔ s / s)║ \<le> a ᣔ b * ln (1 + T / b)"
proof -
  have "║1 / (2*\<pi>*\<i>) * ~\<integral> (linepath (\<complex> b (-T)) (\<complex> b T)) (\<lambda>s. 1 * a ᣔ s / s)║
       \<le> 1 * a ᣔ b * ln (1 + T / b)"
    by (rule perron_aux_3') (auto intro: Ha cond perron_integrable)
  thus ?thesis unfolding path_def by auto
qed

theorem perron_aux':
  assumes Ha: "0 < a"
  shows "║F a║ \<le> a ᣔ b * r a"
proof -
  note assms' = assms cond
  define P where "P \<equiv> 1 / (2*\<pi>*\<i>) * ~\<integral> path (\<lambda>s. a ᣔ s / s)"
  have lm_1: "1 + ln (1 + T / b) \<le> 2 + ln (T / b)"
  proof -
    have "1 \<le> T / b" using hT Hb by auto
    hence "1 + T / b \<le> 2 * (T / b)" by auto
    hence "ln (1 + T / b) \<le> ln 2 + ln (T / b)" by (subst ln_mult [symmetric]) auto
    thus ?thesis using ln_2_less_1 by auto
  qed
  have *: "║F a║ \<le> a ᣔ b * (2 + ln (T / b))"
  proof (cases "1 \<le> a")
    assume Ha': "1 \<le> a"
    have "║P - 1║ \<le> ║P║ + 1" by (simp add: norm_triangle_le_diff)
    also have "\<dots> \<le> a ᣔ b * ln (1 + T / b) + 1"
    proof -
      have "║P║ \<le> a ᣔ b * ln (1 + T / b)"
        unfolding P_def by (intro perron_aux_3 assms')
      thus ?thesis by auto
    qed
    also have "\<dots> \<le> a ᣔ b * (2 + ln (T / b))"
    proof -
      have "1 = a ᣔ 0" using Ha' by auto
      also have "a ᣔ 0 \<le> a ᣔ b" using Ha' Hb by (intro powr_mono) auto
      finally have "a ᣔ b * ln (1 + T / b) + 1 \<le> a ᣔ b * (1 + ln (1 + T / b))"
        by (auto simp add: algebra_simps)
      also have "\<dots> \<le> a ᣔ b * (2 + ln (T / b))" using Ha' lm_1 by auto
      finally show ?thesis .
    qed
    finally show ?thesis using Ha' unfolding F_def P_def by auto
  next
    assume Ha': "\<not> 1 \<le> a"
    hence "║P║ \<le> a ᣔ b * ln (1 + T / b)"
      unfolding P_def by (intro perron_aux_3 assms')
    also have "\<dots> \<le> a ᣔ b * (2 + ln (T / b))"
      by (rule mult_left_mono) (use lm_1 in auto)
    finally show ?thesis using Ha' unfolding F_def P_def by auto
  qed
  consider "0 < a \<and> a \<noteq> 1" | "a = 1" using Ha by linarith
  thus ?thesis proof cases
    define c where "c = 1 / 2 * a ᣔ b / (T * \<bar>ln a\<bar>)"
    assume Ha': "0 < a \<and> a \<noteq> 1"
    hence "(0 < a \<and> a < 1) \<or> a > 1" by auto
    hence "║F a║ \<le> c" unfolding c_def using perron_aux_1 perron_aux_2 by auto
    hence "║F a║ \<le> min c (a ᣔ b * (2 + ln (T / b)))" using * by auto
    also have "\<dots> = a ᣔ b * r a"
      unfolding r_def c_def using Ha' by auto (subst min_mult_distrib_left, auto)
    finally show ?thesis using Ha' unfolding P_def by auto
  next
    assume Ha': "a = 1"
    with * show ?thesis unfolding r_def by auto
  qed
qed

lemma r_bound:
  assumes Hn: "1 \<le> n"
  shows "r (x / n) \<le> H / T + (if n \<in> region then 2 + ln (T / b) else 0)"
proof (cases "n \<in> region")
  assume *: "n \<notin> region"
  then consider "n < x - x / H" | "x + x / H < n" unfolding region_def by auto
  hence "1 / \<bar>ln (x / n)\<bar> \<le> 2 * H"
  proof cases
    have hH': "1 / (1 - 1 / H) > 1" using hH by auto
    case 1 hence "x / n > x / (x - x / H)"
      using Hx hH Hn by (intro divide_strict_left_mono) auto
    also have "x / (x - x / H) = 1 / (1 - 1 / H)"
      using Hx hH by (auto simp add: field_simps)
    finally have xn: "x / n > 1 / (1 - 1 / H)" .
    moreover have xn': "x / n > 1" using xn hH' by linarith
    ultimately have "\<bar>ln (x / n)\<bar> > ln (1 / (1 - 1 / H))"
      using hH Hx Hn by (auto simp add: ln_less_cancel_iff)
    hence "1 / \<bar>ln (x / n)\<bar> < 1 / ln (1 / (1 - 1 / H))"
      using xn' hH' by (intro divide_strict_left_mono mult_pos_pos ln_gt_zero) auto
    also have "\<dots> \<le> H" proof -
      have "ln (1 - 1 / H) \<le> - (1 / H)"
        using hH by (intro ln_one_minus_pos_upper_bound) auto
      hence "-1 / ln (1 - 1 / H) \<le> -1 / (- (1 / H))"
        using hH by (intro divide_left_mono_neg) (auto intro: divide_neg_pos)
      also have "... = H" by auto
      finally show ?thesis
        by (subst (2) inverse_eq_divide [symmetric])
           (subst ln_inverse, use hH in auto)
    qed
    finally show ?thesis using hH by auto
  next
    case 2 hence "x / n < x / (x + x / H)"
      using Hx hH Hn by (auto intro!: divide_strict_left_mono mult_pos_pos add_pos_pos)
    also have "\<dots> = 1 / (1 + 1 / H)"
    proof -
      have "0 < x + x * H" using Hx hH by (auto intro: add_pos_pos)
      thus ?thesis using Hx hH by (auto simp add: field_simps)
    qed
    finally have xn: "x / n < 1 / (1 + 1 / H)" .
    also have hH': "\<dots> < 1" using hH by (auto simp add: field_simps)
    finally have xn': "0 < x / n \<and> x / n < 1" using Hx Hn by auto
    have "1 / \<bar>ln (x / n)\<bar> = -1 / ln (x / n)"
      using xn' by (auto simp add: field_simps)
    also have "\<dots> \<le> 2 * H" proof -
      have "ln (x / n) < ln (1 / (1 + 1 / H))"
        using xn xn' by (subst ln_less_cancel_iff) (blast, linarith)
      also have "\<dots> = - ln (1 + 1 / H)"
        by (subst (1) inverse_eq_divide [symmetric])
           (subst ln_inverse, intro add_pos_pos, use hH in auto)
      also have "\<dots> \<le> - 1 / (2 * H)"
      proof -
        have "1 / H - (1 / H)\<^sup>2 \<le> ln (1 + 1 / H)"
          by (rule ln_one_plus_pos_lower_bound) (use hH in auto)
        hence "- ln (1 + 1 / H) \<le> - 1 / H + (1 / H)\<^sup>2" by auto
        also have "\<dots> \<le> - 1 / (2 * H)"
          using hH unfolding power2_eq_square by (auto simp add: field_simps)
        finally show ?thesis .
      qed
      finally have "-1 / ln (x / n) \<le> -1 / (-1 / (2 * H))"
        by (intro divide_left_mono_neg) (insert xn' hH, auto simp add: field_simps)
      thus ?thesis by auto
    qed
    finally show ?thesis .
  qed
  hence "(1 / \<bar>ln (x / n)\<bar>) / (2 * T) \<le> (2 * H) / (2 * T)"
    using hT' by (intro divide_right_mono) auto
  hence "1 / (2 * T * \<bar>ln (x / n)\<bar>) \<le> H / T"
    by (simp add: field_simps)
  moreover have "x / n \<noteq> 1" using * hH unfolding region_def by auto
  ultimately show ?thesis unfolding r_def using * by auto
next
  assume *: "n \<in> region"
  moreover have "2 + ln (T / b) \<le> H / T + (2 + ln (T / b))"
    using hH hT' by auto
  ultimately show ?thesis unfolding r_def by auto
qed

theorem perron_aux:
  assumes Hn: "0 < n"
  shows "║F' n║ \<le> 1 / n \<nat>ᣔ b * (x ᣔ b * H / T)
    + (if n \<in> region then 3 * (2 + ln (T / b)) else 0)" (is "?P \<le> ?Q")
proof -
  have "║F (x / n)║ \<le> (x / n) ᣔ b * r (x / n)"
    by (rule perron_aux') (use Hx Hn in auto)
  also have "\<dots> \<le> (x / n) ᣔ b * (H / T + (if n \<in> region then 2 + ln (T / b) else 0))"
    by (intro mult_left_mono r_bound) (use Hn in auto)
  also have "\<dots> \<le> ?Q"
  proof -
    have *: "(x / n) ᣔ b * (H / T) = 1 / n \<nat>ᣔ b * (x ᣔ b * H / T)"
      using Hx Hn by (subst powr_divide) (auto simp add: field_simps)
    moreover have "(x / n) ᣔ b * (H / T + (2 + ln (T / b)))
      \<le> 1 / n \<nat>ᣔ b * (x ᣔ b * H / T) + 3 * (2 + ln (T / b))"
      when Hn': "n \<in> region"
    proof -
      have "(x / n) ᣔ b \<le> 3"
      proof -
        have "x - x / H \<le> n" using Hn' unfolding region_def by auto
        moreover have "x / H < x / 1" using hH Hx by (intro divide_strict_left_mono) auto
        ultimately have "x / n \<le> x / (x - x / H)"
          using Hx hH Hn by (intro divide_left_mono mult_pos_pos) auto
        also have "\<dots> = 1 + 1 / (H - 1)"
          using Hx hH by (auto simp add: field_simps)
        finally have "(x / n) ᣔ b \<le> (1 + 1 / (H - 1)) ᣔ b"
          using Hx Hn Hb by (intro powr_mono2) auto
        also have "\<dots> \<le> exp (b / (H - 1))"
        proof -
          have "ln (1 + 1 / (H - 1)) \<le> 1 / (H - 1)"
            using hH by (intro ln_add_one_self_le_self) auto
          hence "b * ln (1 + 1 / (H - 1)) \<le> b * (1 / (H - 1))"
            using Hb by (intro mult_left_mono) auto
          thus ?thesis unfolding powr_def by auto
        qed
        also have "\<dots> \<le> exp 1" using Hb hH' by auto
        also have "\<dots> \<le> 3" by (rule exp_le)
        finally show ?thesis .
      qed
      moreover have "0 \<le> ln (T / b)" using hT Hb by (auto intro!: ln_ge_zero)
      ultimately show ?thesis using hT
        by (subst ring_distribs, subst *, subst add_le_cancel_left)
           (intro mult_right_mono, auto intro!: add_nonneg_nonneg)
    qed
    ultimately show ?thesis by auto
  qed
  finally show ?thesis unfolding F'_def .
qed

definition a where "a n \<equiv> d\<^sub>n f n"

theorem finite_region: "finite region"
  unfolding region_def by (subst nat_le_real_iff) auto

theorem zero_notin_region: "0 \<notin> region"
  unfolding region_def using hH Hx by (auto simp add: field_simps)

theorem perron_bound:
  "║\<Sum>`n \<ge> 1. a n * F' n║ \<le> x ᣔ b * H * B / T
    + 3 * (2 + ln (T / b)) * (\<Sum>n\<in>region. ║a n║)"
proof -
  define M where "M \<equiv> 3 * (2 + ln (T / b))"
  have sum_1: "(\<lambda>n. ║a n / n \<nat>ᣔ (b :: \<complex>)║) subsummable {1..}"
    unfolding a_def
    by (fold nat_power_complex_def)
       (intro fds_abs_subsummable fds_abs_converges, auto, rule Hb')
  hence sum_2: "(\<lambda>n. ║a n║ * 1 / n \<nat>ᣔ b) subsummable {1..}"
  proof -
    have "║a n / n \<nat>ᣔ (b :: \<complex>)║ = ║a n║ * 1 / n \<nat>ᣔ b" for n
      by (auto simp add: norm_divide field_simps norm_nat_power)
    thus ?thesis using sum_1 by auto
  qed
  hence sum_3: "(\<lambda>n. ║a n║ * 1 / n \<nat>ᣔ b * (x ᣔ b * H / T)) subsummable {1..}"
    by (rule subsummable_mult2)
  moreover have sum_4: "(\<lambda>n. if n \<in> region then M * ║a n║ else 0) subsummable {1..}"
    by (intro has_subsum_summable, rule has_subsum_If_finite)
       (insert finite_region, auto)
  moreover have "║a n * F' n║
    \<le> ║a n║ * 1 / n \<nat>ᣔ b * (x ᣔ b * H / T)
    + (if n \<in> region then M * ║a n║ else 0)" (is "?x' \<le> ?x")
    when "n \<in> {1..}" for n
  proof -
    have "║a n * F' n║ \<le> ║a n║ *
      (1 / n \<nat>ᣔ b * (x ᣔ b * H / T) + (if n \<in> region then M else 0))"
      unfolding M_def
      by (subst norm_mult)
         (intro mult_left_mono perron_aux, use that in auto)
    also have "\<dots> = ?x" by (simp add: field_simps)
    finally show ?thesis .
  qed
  ultimately have "║\<Sum>`n \<ge> 1. a n * F' n║
    \<le> (\<Sum>`n \<ge> 1. ║a n║ * 1 / n \<nat>ᣔ b * (x ᣔ b * H / T)
    + (if n \<in> region then M * ║a n║ else 0))"
    by (intro subsum_norm_bound subsummable_add)
  also have "\<dots> \<le> x ᣔ b * H * B / T + M * (\<Sum>n\<in>region. ║a n║)"
  proof -
    have "(\<Sum>`n \<ge> 1. (if n \<in> region then M * ║a n║ else 0))
        = (\<Sum>n \<in> region \<inter> {1..}. M * ║a n║)"
      by (intro subsumI [symmetric] has_subsum_If_finite_set finite_region)
    also have "\<dots> = M * (\<Sum>n\<in>region. ║a n║)"
    proof -
      have "region \<inter> {1..} = region"
        using zero_notin_region zero_less_iff_neq_zero by (auto intro: Suc_leI)
      thus ?thesis by (subst sum_distrib_left) (use zero_notin_region in auto)
    qed
    also have
      "(\<Sum>`n \<ge> 1. ║a n║ * 1 / n \<nat>ᣔ b * (x ᣔ b * H / T))
      \<le> x ᣔ b * H * B / T"
      by (subst subsum_mult2, rule sum_2, insert hB hH hT', fold a_def)
         (auto simp add: field_simps, subst (1) mult.commute, auto intro: mult_right_mono)
    ultimately show ?thesis
      by (subst subsum_add [symmetric]) ((rule sum_3 sum_4)+, auto)
  qed
  finally show ?thesis unfolding M_def .
qed

lemma path_image_conv:
  assumes "s \<in> img_path"
  shows "conv_abscissa f < s \<bullet> 1"
proof -
  from assms have "Re s = b"
    unfolding img_path_def path_def
    by (auto simp add: closed_segment_def legacy_Complex_simps field_simps)
  thus ?thesis using Hb' conv_le_abs_conv_abscissa [of f] by auto
qed

lemma converge_on_path:
  assumes "s \<in> img_path"
  shows "fds_converges f s"
  by (intro fds_converges path_image_conv assms)

lemma summable_on_path:
  assumes "s \<in> img_path"
  shows "(\<lambda>n. a n / n \<nat>ᣔ s) subsummable {1..}"
  unfolding a_def by (intro eval_fds_complex_subsum(2) converge_on_path assms)

lemma zero_notin_path:
  shows "0 \<notin> closed_segment (\<complex> b (- T)) (\<complex> b T)"
  using Hb unfolding img_path_def path_def
  by (auto simp add: closed_segment_def legacy_Complex_simps field_simps)

theorem perron:
  "(\<lambda>s. eval_fds f s * x ᣔ s / s) \<llangle>~\<integral>\<rrangle> path"
  "║sum_upto a x - 1 / (2*\<pi>*\<i>) * ~\<integral> path (\<lambda>s. eval_fds f s * x ᣔ s / s)║
    \<le> x ᣔ b * H * B / T + 3 * (2 + ln (T / b)) * (\<Sum>n\<in>region. ║a n║)"
proof (goal_cases)
  define g where "g s \<equiv> eval_fds f s * x ᣔ s / s" for s :: \<complex>
  define h where "h s n \<equiv> a n / n \<nat>ᣔ s * (x ᣔ s / s)" for s :: \<complex> and n
  define G where "G n \<equiv> ~\<integral> path (\<lambda>s. (x / n) ᣔ s / s)" for n :: \<nat>
  define H where "H n \<equiv> 1 / (2*\<pi>*\<i>) * G n" for n :: \<nat>
  have h_integrable: "(\<lambda>s. h s n) \<llangle>~\<integral>\<rrangle> path" when "0 < n" for n s
    using Hb Hx unfolding path_def h_def
    by (intro contour_integrable_continuous_linepath continuous_intros)
       (use that zero_notin_path in auto)
  have "~\<integral> path g = ~\<integral> path (\<lambda>s. \<Sum>`n \<ge> 1. h s n)"
  proof (rule contour_integral_eq, fold img_path_def)
    fix s assume *: "s \<in> img_path"
    hence "g s = (\<Sum>`n \<ge> 1. a n / n \<nat>ᣔ s) * (x ᣔ s / s)"
      unfolding g_def a_def
      by (subst eval_fds_complex_subsum) (auto intro!: converge_on_path)
    also have "\<dots> = (\<Sum>`n \<ge> 1. a n / n \<nat>ᣔ s * (x ᣔ s / s))"
      by (intro subsum_mult2 [symmetric] summable) (intro summable_on_path *)
    finally show "g s = (\<Sum>`n \<ge> 1. h s n)" unfolding h_def .
  qed
  also have
    sum_1: "(\<lambda>n. ~\<integral> path (\<lambda>s. h s n)) subsummable {1..}"
    and "\<dots> = (\<Sum>`n \<ge> 1. ~\<integral> path (\<lambda>s. h s n))"
  proof (goal_cases)
    have "((\<lambda>N. ~\<integral> path (\<lambda>s. sum (h s) {1..N})) \<longlongrightarrow> ~\<integral> path (\<lambda>s. subsum (h s) {1..})) +\<infinity>"
    proof (rule contour_integral_uniform_limit)
      show "valid_path path" unfolding path_def by auto
      show "sequentially \<noteq> bot" by auto
    next
      fix t :: \<real>
      show "║vector_derivative path (at t)║ \<le> \<surd> (4 * T\<^sup>2)"
        unfolding path_def by (auto simp add: legacy_Complex_simps)
    next
      from path_image_conv
      have *: "uniformly_convergent_on img_path (\<lambda>N s. \<Sum>n\<le>N. d\<^sub>n f n / nat_power n s)"
        by (intro uniformly_convergent_eval_fds) (unfold path_def img_path_def, auto)
      have *: "uniformly_convergent_on img_path (\<lambda>N s. \<Sum>n = 1..N. a n / n \<nat>ᣔ s)"
      proof -
        have "(\<Sum>n\<le>N. d\<^sub>n f n / nat_power n s) = (\<Sum>n = 1..N. a n / n \<nat>ᣔ s)" for N s
        proof -
          have "(\<Sum>n\<le>N. d\<^sub>n f n / nat_power n s) = (\<Sum>n\<le>N. a n / n \<nat>ᣔ s)"
            unfolding a_def nat_power_complex_def by auto
          also have "\<dots> = (\<Sum>n\<in>{..N} - {0}. a n / n \<nat>ᣔ s)"
            by (subst sum_diff1) auto
          also have "\<dots> = (\<Sum>n = 1..N. a n / n \<nat>ᣔ s)"
          proof -
            have "{..N} - {0} = {1..N}" by auto
            thus ?thesis by auto
          qed
          finally show ?thesis by auto
        qed
        thus ?thesis using * by auto
      qed
      hence "uniform_limit img_path
        (\<lambda>N s. \<Sum>n = 1..N. a n / n \<nat>ᣔ s)
        (\<lambda>s. \<Sum>`n \<ge> 1. a n / n \<nat>ᣔ s) +\<infinity>"
      proof -
        have "uniform_limit img_path
          (\<lambda>N s. \<Sum>n = 1..N. a n / n \<nat>ᣔ s)
          (\<lambda>s. lim (\<lambda>N. \<Sum>n = 1..N. a n / n \<nat>ᣔ s)) +\<infinity>"
          using * by (subst (asm) uniformly_convergent_uniform_limit_iff)
        moreover have "lim (\<lambda>N. \<Sum>n = 1..N. a n / n \<nat>ᣔ s) = (\<Sum>`n \<ge> 1. a n / n \<nat>ᣔ s)" for s
          by (rule subsum_ge_limit)
        ultimately show ?thesis by auto
      qed
      moreover have "bounded ((\<lambda>s. subsum (\<lambda>n. a n / n \<nat>ᣔ s) {1..}) ` img_path)" (is "bounded ?A")
      proof -
        have "bounded (eval_fds f ` img_path)"
          by (intro compact_imp_bounded compact_continuous_image continuous_on_eval_fds)
             (use path_image_conv img_path_def path_def in auto)
        moreover have "\<dots> = ?A"
          unfolding a_def by (intro image_cong refl eval_fds_complex_subsum(1) converge_on_path)
        ultimately show ?thesis by auto
      qed
      moreover have "bounded ((\<lambda>s. x ᣔ s / s) ` img_path)"
        unfolding img_path_def path_def
        by (intro compact_imp_bounded compact_continuous_image continuous_intros, auto)
           (use Hx in auto, use Hb in \<open>auto simp add: closed_segment_def legacy_Complex_simps algebra_simps\<close>)
      ultimately have "uniform_limit img_path
        (\<lambda>N s. (\<Sum>n = 1..N. a n / n \<nat>ᣔ s) * (x ᣔ s / s))
        (\<lambda>s. (\<Sum>`n \<ge> 1. a n / n \<nat>ᣔ s) * (x ᣔ s / s)) +\<infinity>" (is ?P)
        by (intro uniform_lim_mult uniform_limit_const)
      moreover have "?P = uniform_limit (path_image path)
        (\<lambda>N s. sum (h s) {1..N}) (\<lambda>s. subsum (h s) {1..}) +\<infinity>" (is "?P = ?Q")
        unfolding h_def
        by (fold img_path_def, rule uniform_limit_cong', subst sum_distrib_right [symmetric], rule refl)
           (subst subsum_mult2, intro summable_on_path, auto)
      ultimately show ?Q by blast
    next
      from h_integrable
      show "\<forall>\<^sub>F N in +\<infinity>. (\<lambda>s. sum (h s) {1..N}) \<llangle>~\<integral>\<rrangle> path"
        unfolding h_def by (intro eventuallyI contour_integrable_sum) auto
    qed
    hence *: "has_subsum (\<lambda>n. ~\<integral> path (\<lambda>s. h s n)) {1..} (~\<integral> path (\<lambda>s. subsum (h s) {1..}))"
      using h_integrable by (subst (asm) contour_integral_sum) (auto intro: has_subsum_ge_limit)
    case 1 from * show ?case unfolding h_def by (intro has_subsum_summable)
    case 2 from * show ?case unfolding h_def by (rule subsumI)
  qed
  note this(2) also have
    sum_2: "(\<lambda>n. a n * G n) subsummable {1..}"
    and "\<dots> = (\<Sum>`n \<ge> 1. a n * G n)"
  proof (goal_cases)
    have *: "a n * G n = ~\<integral> path (\<lambda>s. h s n)" when Hn: "n \<in> {1..}" for n :: \<nat>
    proof -
      have "(\<lambda>s. (x / n) ᣔ s / s) \<llangle>~\<integral>\<rrangle> path"
        unfolding path_def by (rule perron_integrable) (use Hn Hx hT in auto)
      moreover have "~\<integral> path (\<lambda>s. h s n) = ~\<integral> path (\<lambda>s. a n * ((x / n) ᣔ s / s))"
      proof (intro contour_integral_cong refl)
        fix s :: \<complex>
        have "(x / n) ᣔ s * n ᣔ s = ((x / n :: \<complex>) * n) ᣔ s"
          by (rule powr_times_real [symmetric]) (use Hn Hx in auto)
        also have "\<dots> = x ᣔ s" using Hn by auto
        finally have "(x / n) ᣔ s = x ᣔ s / n ᣔ s" using Hn by (intro eq_divide_imp) auto
        thus "h s n = a n * ((x / n) ᣔ s / s)" unfolding h_def by (auto simp add: field_simps)
      qed
      ultimately show ?thesis unfolding G_def by (subst (asm) contour_integral_lmul) auto
    qed
    case 1 show ?case by (subst subsummable_cong) (use * sum_1 in auto)
    case 2 show ?case by (intro subsum_cong * [symmetric])
  qed
  note this(2) finally have
    "1 / (2*\<pi>*\<i>) * ~\<integral> path g = (\<Sum>`n \<ge> 1. a n * G n) * (1 / (2*\<pi>*\<i>))" by auto
  also have
    sum_3: "(\<lambda>n. a n * G n * (1 / (2*\<pi>*\<i>))) subsummable {1..}"
    and "\<dots> = (\<Sum>`n \<ge> 1. a n * G n * (1 / (2*\<pi>*\<i>)))"
    by (intro subsummable_mult2 subsum_mult2 [symmetric] sum_2)+
  note this(2) also have
    sum_4: "(\<lambda>n. a n * H n) subsummable {1..}"
    and "\<dots> = (\<Sum>`n \<ge> 1. a n * H n)"
    unfolding H_def using sum_3 by auto
  note this(2) also have
    "\<dots> - (\<Sum>`n \<ge> 1. if n \<le> x then a n else 0)
      = (\<Sum>`n \<ge> 1. a n * H n - (if n \<le> x then a n else 0))"
    using sum_4
    by (rule subsum_minus(1), unfold subsummable_def)
       (auto simp add: if_if_eq_conj nat_le_real_iff intro!: summable_If_finite)
  moreover have "(\<Sum>`n \<ge> 1. if n \<le> x then a n else 0) = sum_upto a x"
  proof -
    have "(\<Sum>`n \<ge> 1. if n \<le> x then a n else 0) = (\<Sum>n :: \<nat>|n \<in> {1..} \<and> n \<le> x. a n)"
      by (intro subsumI [symmetric] has_subsum_If_finite) (auto simp add: nat_le_real_iff)
    also have "\<dots> = sum_upto a x"
    proof -
      have "{n :: \<nat>. n \<in> {1..} \<and> n \<le> x} = {n. 0 < n \<and> n \<le> x}" by auto
      thus ?thesis unfolding sum_upto_def by auto
    qed
    finally show ?thesis .
  qed
  moreover have "(\<Sum>`n \<ge> 1. a n * H n - (if n \<le> x then a n else 0)) = (\<Sum>`n \<ge> 1. a n * F' n)"
    unfolding F_def F'_def G_def H_def by (rule subsum_cong) (auto simp add: algebra_simps)
  ultimately have result: "║sum_upto a x - 1 / (2*\<pi>*\<i>) * ~\<integral> path g║ = ║\<Sum>`n \<ge> 1. a n * F' n║"
    by (subst norm_minus_commute) auto
  case 1 show ?case
  proof -
    have "closed_segment (\<complex> b (- T)) (\<complex> b T) \<subseteq> {s. conv_abscissa f < ereal (s \<bullet> 1)}"
      using path_image_conv unfolding img_path_def path_def by auto
    thus ?thesis unfolding path_def
      by (intro contour_integrable_continuous_linepath continuous_intros)
         (use Hx zero_notin_path in auto)
  qed
  case 2 show ?case using perron_bound result unfolding g_def by linarith
qed
end

theorem perron_formula:
  fixes b B H T x :: \<real> and f :: "\<complex> fds"
  assumes Hb: "0 < b" and hT: "b \<le> T"
    and Hb': "abs_conv_abscissa f < b"
    and hH: "2 \<le> H" and hH': "b + 1 \<le> H" and Hx: "2 \<le> x"
    and hB: "(\<Sum>`n \<ge> 1. ║d\<^sub>n f n║ / n \<nat>ᣔ b) \<le> B"
  shows "(\<lambda>s. eval_fds f s * x ᣔ s / s) \<llangle>~\<integral>\<rrangle> (linepath (\<complex> b (-T)) (\<complex> b T))"
        "║sum_upto (d\<^sub>n f) x - 1 / (2*\<pi>*\<i>) * ~\<integral> (linepath (\<complex> b (-T)) (\<complex> b T)) (\<lambda>s. eval_fds f s * x ᣔ s / s)║
         \<le> x ᣔ b * H * B / T + 3 * (2 + ln (T / b)) * (\<Sum>n | x - x / H \<le> n \<and> n \<le> x + x / H. ║d\<^sub>n f n║)"
proof (goal_cases)
  interpret z: perron_locale using assms unfolding perron_locale_def by auto
  case 1 show ?case using z.perron(1) unfolding z.path_def .
  case 2 show ?case using z.perron(2) unfolding z.path_def z.region_def z.a_def .
qed
end
