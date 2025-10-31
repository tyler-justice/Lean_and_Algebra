import Mathlib

/-
第一回
- Intro
- 画面共有
- Live.Lean を見せる (少し時間がかかることも伝える)
-/

/-
Lean とは何か
- Microsoft によって開発された関数型プログラミング言語である.
- 数学の種々の定理を証明「することも出来る」
-/

/-
Lean の特徴
- 関数型」プログラミング : プログラムは項と関数からなる.
- 項にはすべて「型」がある.
- 項から項に対応をつけるのが Lean の関数
-/

/-
Lean の「正しさ」について
- Lean は無矛盾, すなわち同時にある定理 A とその定理 A の否定が証明されることはないか?
- Lean ver. 3 までは以下のことが証明されていた.
  - Lean ver. 3 は ZFC + 到達不可能基数の存在と相対的に無矛盾, すなわち Lean が無矛盾であれば ZFC + 到達不可能基数も無矛盾, 逆も成り立つ.
  - これは ZFC + 到達不可能基数の存在を Lean の code でプログラム化し, 逆に Lean の公理を ZFC + 到達不可能基数の存在の公理で書くことに酔って示された.
- 2025 年現在 Lean の version は 4.18.
- この版の Lean の公理はまだ ZFC + 到達不可能基数の存在の公理で表すことが出来ていない (逆は出来ている)
- この問題に取り組むことは興味があるが, 自分には出来ない (指導も難しい)
-/


/-
Question
  Lean で定理 A をエラーを出すことなく形式化出来たとする. 一方, 定理 A の主張の反例を普通の数学 ZFC の公理から構成できたとする. この時どのようなことが結論出来るか?

Answer
  Lean で ZFC の公理を記述出来るので, 定理 A とその否定が共に Lean で証明出来る, すなわち Lean は無矛盾ではない. Lean と ZFC + 到達不可能基数の存在の無矛盾性の等価性から ZFC + 到達不可能基数も無矛盾ではないことがわかる.
-/



/-
Lean での定理, 定義, 例などの読み方
- Lean での定理等は以下のような形をしている.
theorem 名前 仮定の項 : 主張の項 := 詳細
def 名前 仮定の項 : 定義された項の型 := 詳細
ここで詳細のところは
  - 定理 : 仮定の項を主張の項の変換する「関数」を記述することになる.
  - 定義 : 仮定の項か定義された項がどう定まるか? という「関数」を記述することになる.
-/

/- 以下の (a b c : ℝ ) は a b c は型 ℝ を持つという意味. この「型」の概念は言葉で説明するのが難しい. 四回の講義で感覚を掴んでもらいたい. とりあえず (a b c : ℝ) は a,b,c ∈ ℝ と考えて欲しい-/

/-
 Lean では演算は左結合である. すなわち
 a*b*c*d = ((a*b)*c)+d
 となる.
-/

variable (a b c : ℝ)

example (a b c : ℝ) : a * b * c = b * (a * c) := by
  rw [mul_comm a b]
  rw [mul_assoc b a c]

example (a b c : ℝ) : c * b * a = b * (a * c) := by
  sorry

/-
 成績評価はこのような sorry を含む example を出すので, プログラムを書いて Moodle に投稿してもらい, エラーが出ない場合, 正解とみなして加点する.
-/

/- 関数の説明 -/

#check pow_two a
#check mul_sub a b c
#check add_mul a b c
#check add_sub a b c
#check sub_sub a b c
#check add_zero a
#check zero_add a

/-
  これらを使い, 中学数学を形式化してみる.
-/

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
  rw [mul_add, add_mul, add_mul]
  rw [← add_assoc, add_assoc (a * a)]
  rw [mul_comm b a, ← two_mul]



example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
  calc
    (a + b) * (a + b) = a * a + b * a + (a * b + b * b) := by
      rw [mul_add, add_mul, add_mul]
    _ = a * a + (b * a + a * b) + b * b := by
      rw [← add_assoc, add_assoc (a * a)]
    _ = a * a + 2 * (a * b) + b * b := by
      rw [mul_comm b a, ← two_mul]

/- rewrite で示す -/
example : (a - b)^2 = a^2 - 2*a*b + b^2 := by sorry

/- calc を使う -/
example : (a - b)^2 = a^2 - 2*a*b + b^2 := by sorry

/- 課題 -/
example  : a^2 - b^2 = (a -b)*(a + b) := by ring


/- 課題 -/

example : (a + b + c)*(a^2 + b^2 + c^2 - a - b -c) = a^3 + b^3 + c^3 - 3*a*b*c := by
  sorry

/- Lean ではすべての証明は等価なものとして扱われる. つまり, 上の example を ring で済ませても 結合律などを丁寧に適用してやっても同じとみなす. -/

/- 仮定を利用する -/
example (d : ℝ ) (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp, hyp']
  ring


variable (x y : ℝ)

example (h : 2*x + 1 = 3) : x = 1 := by
  calc
    _  = (1/2)*(2*x + 1) - 1/2 := by ring
    _  = (1/2)*3 - 1/2 := by rw [h]
    _ = 1 := by norm_num

example (h1 : 2 * x - y = 4) (h2 : y - x + 1 = 2) : x = 5 := by
  sorry

example (h1 : 2 * x - y = 4) (h2 : y - x + 1 = 2) : y = 6 := by
  sorry

#check eq_zero_or_eq_zero_of_mul_eq_zero
#check eq_neg_add_iff_add_eq
#check eq_of_sub_eq_zero


example (h1 : x^2 - 3*x + 2 = 0) : x = 1 ∨ x = 2 := by
  have h2 : x^2 - 3*x + 2 = (x-1)*(x-2) := by ring
  rw [h2] at h1
  rcases eq_zero_or_eq_zero_of_mul_eq_zero h1 with A|B
  · left
    exact eq_of_sub_eq_zero A
  · right
    exact eq_of_sub_eq_zero B

example (h1 : a*x^2 + b*x + c = 0) (h2 : a ≠ 0): x = (-b + √(b^2 - 4*a*c))/2 ∨ x = (-b - √(b^2 - 4*a*c))/2 := by sorry


example (h1 : x^3 - 6*x^2 + 11*x -6 = 0) : x = 1 ∨ x = 2 ∨ x = 3 := by sorry


/-
  式変形する適切な関数をどのように見つけるか? は Lean をこれまで五年間扱ってきてもまだ有効な方法がわからない.
  Loogle
-/
