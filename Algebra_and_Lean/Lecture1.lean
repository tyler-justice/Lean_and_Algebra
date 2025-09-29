import Mathlib

/-
第一回
- Lean の紹介
- 等式の証明
- 不等式の証明
- 仮定の利用
- Reason Backward
- 定理, 補題の利用
- 不等式の証明
-/

/-
Lean とは何か
- Microsoft によって開発された関数型プログラミング言語である.
- 数学の種々の定理を証明「することも出来る」.
- プログラムを書いて何かを計算させることももちろん出来る.
-/

/-
Lean の特徴
- 関数型」プログラミング : プログラムは項と関数からなる.
- 項にはすべて「型」がある.
- 型から型に対応をつけるのが Lean の関数
-/

/-
Lean の「正しさ」について
- Lean は無矛盾, すなわち同時にある定理 A とその定理 A の否定が証明されることはないか?
- Lean ver. 3 までは以下のことが証明されていた.
  - Lean ver. 3 は ZFC + 到達不可能基数の存在と相対的に無矛盾, すなわち Lean が無矛盾であれば ZFC + 到達不可能基数も無矛盾, 逆も成り立つ.
  - これは ZFC + 到達不可能基数の存在を Lean の code でプログラム化し, 逆に Lean の公理を ZFC + 到達不可能基数の存在の公理で書くことによって示された.
- 2025 年 9 月現在 Lean の version は 4.24.
- この版の Lean の公理はまだ ZFC + 到達不可能基数の存在の公理で表すことが出来ていない (逆は出来ている)
- ver. 3 のような soundness (健全性) を示すために二つのプロジェクトが進行中.
- 一つは Lean の公理を ZFC + 到達不可能基数の存在で記述する, 少なくとも Lean のどの公理が記述出来るかを明らかにする. コンピューターの利点である証明がどの公理に依存しているかを確認するのは比較的容易なので, これは安全という公理をリストアップすることが出来れば, それだけを使って証明を書くというやり方で「健全」な証明が得られる.
- もう一つは Lean を検証するプログラムを書くというもの. こちらは確かに二種類の方法で検証されている, ということで信頼度は上がるが, 健全性を示すことにはならない.
-/


/-
Question
  Lean ver.3 で定理 A をエラーを出すことなく形式化出来たとする. 一方, 定理 A の主張の反例を普通の数学 ZFC の公理から構成できたとする. この時どのようなことが結論出来るか?

Answer
  Lean ver.3 で ZFC の公理を記述出来るので, 定理 A とその否定が共に Lean で証明出来る, すなわち Lean は無矛盾ではない. Lean と ZFC + 到達不可能基数の存在の無矛盾性の等価性から ZFC + 到達不可能基数も無矛盾ではないことがわかる.
-/


/-
Lean での定理, 定義, 例などの読み方
- Lean での定理等は以下のような形をしている.

theorem 名前 仮定の項 : 主張の項 := 詳細
def 名前 仮定の項 : 定義された項の型 := 詳細
example (名前 : 省略可) 仮定の項 : 主張の項 := 詳細

ここで詳細のところは
  - 定理 : 仮定の項を主張の項の変換する「関数」を記述することになる.
  - 定義 : 仮定の項か定義された項がどう定まるか? という「関数」を記述する.
  - 例 : 定理と同じで仮定の項を主張の項に変換する「関数」を記述する.
-/

/- 以下の (a b c : ℝ ) は a b c は型 ℝ を持つという意味. この「型」の概念は言葉で説明するのが難しい. とりあえず (a b c : ℝ) は a,b,c ∈ ℝ と考えて欲しい-/

/-
 Lean では演算は左結合である. すなわち
 a*b*c*d = ((a*b)*c)+d
 となる.
-/



example (a b c : ℝ) : a * b * c = b * (a * c) := by
  rw [mul_comm a b]
  rw [mul_assoc b a c]

example (a b c : ℝ) : c * b * a = b * (a * c) := by
  sorry

example (a b : ℝ) : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
  rw [mul_add, add_mul, add_mul]
  rw [← add_assoc, add_assoc (a * a)]
  rw [mul_comm b a, ← two_mul]



example (a b : ℝ) : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
  calc
    (a + b) * (a + b) = a * a + b * a + (a * b + b * b) := by
      rw [mul_add, add_mul, add_mul]
    _ = a * a + (b * a + a * b) + b * b := by
      rw [← add_assoc, add_assoc (a * a)]
    _ = a * a + 2 * (a * b) + b * b := by
      rw [mul_comm b a, ← two_mul]

variable (a b c : ℝ)

  /- rewrite で示す -/
example : (a - b)^2 = a^2 - 2*a*b + b^2 := by sorry

/- calc を使う -/
example : (a - b)^2 = a^2 - 2*a*b + b^2 := by sorry

/- 課題 -/
example  : a^2 - b^2 = (a -b)*(a + b) := by sorry


/- Lean ではすべての証明は等価なものとして扱われる. つまり, 上の example を ring で済ませても 結合律などを丁寧に適用してやっても同じとみなす. -/



/- 課題 -/

example : (a + b + c)*(a^2 + b^2 + c^2 - a - b -c) = a^3 + b^3 + c^3 - 3*a*b*c := by
  sorry

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
