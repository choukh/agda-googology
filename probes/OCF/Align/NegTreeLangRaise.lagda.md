# 树的语言, 否定一路 (三): 升界判据 `Raise` 的盲区与边界

> 不含记号. 入口 [NegTreeLang](NegTreeLang.lagda.md). 对着接口 [TreeLangIf](TreeLangIf.lagda.md) §5 ("接口定稿 2026-11-05 20:27 (首次编译通过)", 变更记录: 无) 写, 导入它, 不另造接口; 只读导入构造一路的 [TreeLangRaise](TreeLangRaise.lagda.md) 以检查它的形状定理. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用函数外延, 不用 UIP.
>
> **构造一路的形状定理.** `TreeLangRaise`: `ev→wdec` (律的定义域里的一对成员, 键弱可判定), `shape`/`unique` (定义域里升界在读数上唯一), `sup-bare→Sep` (`Lev` 的裸坐标积世界, `Ev` 恒真, 推出分离子), `Pos.posR`/`pos-unique` (下标取字面位置: 存在且唯一). 推出的形状 (它的判断): "Ω-并只取有界坐标".
>
> **结果.**
>
> 1. **`shrink`, `empty-raise` (定理, 盲: `Raise` 对 `Ev` 向下封闭).** 把律的定义域 `Ev` 缩小, 合法的升界仍合法; `Ev` 取空时恒等就是合法升界. 接口没有说 `Ev` 至少要含哪些对.
> 2. **`diag-raise`, `diag-moves`, `bare-vs-diag` (定理, 盲).** `TreeLangRaise.supF` (`Lev` 的裸坐标积世界) 只改 `Ev` 为 "同一成员" (`supD`): 有合法升界 (`NegGenFoldUpd.rB` 把一切分量的底拷贝一起升), 它把**一切**成员的读数都改成 $v$. 同一个世界, 成员, 键, 读数, 定义域一大 (`Ev = ⊤`) 推出分离子, 定义域一小就有实例. 所以 "Ω-并只取有界坐标" 不是 `Raise` 推出的, 是 "定义域要含异键的成员对" 这一条额外要求推出的; 接口没有这一条.
> 3. **`raise-iso`, `raise-adj`, `no-frame-SL01`, `raise-tag` (定理, 边界).** `Raise` 的读数类型 $V$ 对一切成员相同, 而 `set` 对**一切** $v:V$. 所以定义域含 $(j,j)$ 的成员 $j$, 若读数经某个类型 $X$ 分解且有左逆 (`Fac`), 则 $X\cong V$ (`raise-iso`). 两个这样的成员, 一个的 $X$ 是 `HB S′`, 另一个的 $X$ 是 `S′` 的某个种类的坐标 (相邻两级), 就矛盾 (`raise-adj`, 由 `no-retract`). 实例: `SL` 的第 0 层与第 1 层的新种类不能同在一个这样的框架里 (`no-frame-SL01`). 把 $V$ 换成带标签的和 ($\Sigma$ 层号) 也不行: 定义域含 $(j,j)$ 的成员的读数取遍 $V$ (`raise-onto`), 所以读数的标签不能固定 (`raise-tag`). `TreeLangRaise` 文件头说 "框架读数类型 $V$ 不随成员变, 所以不碰跨级"; 本篇把它加强成定理: **`Raise` 的框架装不下跨级的成员** (在 `Fac` 的意义下).
> 4. **`any-lowers` (定理, 盲).** `Raise` 没有 "世界变大" 的律: 在构造一路自己的实例框架 (`posInst` 的框架) 上, **任一**合法升界都把一个读数从 $1$ 改成 $0$. 对照 `RsOwnIf.RsK` 有 `rs≤`. 所以 `Raise` 是 "置值" 的判据, 不是 "升界" 的判据.
>
> **前提实例.** `fac-id` (任一成员经 $X=V$ 分解); `posSelf` (`posInst` 的框架: 定义域含 $(j,j)$); `facL`, `facH`: 两个框架 (`Pos` 取 $V=$ `HB (Lv lz)` 或 `HB (Lv (ls lz))`), 各有合法升界与分解, `raise-adj` 的前提各半可满足; 合起来正是被否定的.
>
> **只否定什么.** 只否定: (2) 推断 "`Raise` 推出 Ω-并只取有界坐标" (要额外的定义域要求); (3) 一个框架同时装下相邻两级、读数经各自坐标类型分解 (有左逆)、定义域含自身对; (4) 推断 "`Raise` 的实例是升界". **不否定**: 构造一路的任何定理 (`ev→wdec`, `shape`, `unique`, `sup-bare→Sep`, `pos-unique` 都对); 读数无左逆的有损分解; 每一级各一个框架 (同级成员); 在框架外另加 `≤` 的律.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegTreeLangRaise where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import OCF.Align.CumReadCF using (A; azero; asuc)
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerFTree using (H₀)
open import OCF.Align.HtTowerNeg using (no-retract)
open import OCF.Align.NegGenFoldUpd using (rB; Sep)
open import OCF.Align.LFReTy using (Lv; lz; ls)
open import OCF.Align.TreeLangIf
import OCF.Align.TreeLangRaise as TR
```

## §1 `Raise` 对定义域向下封闭

`withEv F Ev′`: 同一个框架, 换定义域.

```agda
withEv : (F : RaiseFrame) → (W F → J F → J F → Set) → RaiseFrame
withEv F Ev′ = record { W = W F ; J = J F ; Key = Key F ; V = V F ; key = key F ; obs = obs F ; Ev = Ev′ }

shrink : ∀ {F} (Ev′ : W F → J F → J F → Set) → (∀ {w j j′} → Ev′ w j j′ → Ev F w j j′) → Raise F → Raise (withEv F Ev′)
shrink Ev′ sub R = record
  { rs = rs R
  ; set = λ v e k → set R v (sub e) k
  ; keep = λ v e nk → keep R v (sub e) nk }

empty-raise : ∀ F → Raise (withEv F (λ _ _ _ → ⊥))
empty-raise F = record { rs = λ w j v → w ; set = λ v () ; keep = λ v () }
```

## §2 `Lev` 的裸坐标积世界: 定义域只含同一成员时有实例

`supD`: 与 `TreeLangRaise.supF` 只差 `Ev` (那里恒真, 这里 "$j'$ 就是 $j$"). 升界: 每个分量里每一份底拷贝都换成 $v$ (`rB`, 对层号结构递归, 不判定下标).

```agda
supD : RaiseFrame
supD = withEv TR.supF (λ _ j j′ → j′ ≡ j)

base-rB : ∀ {S : KS} (c : HB S) v w → TR.baseBd c (rB c v w) ≡ v
base-rB hz v w = refl
base-rB (hs x) v w = base-rB x v (proj₁ w)
base-rB (hl f) v w = base-rB (f 0) v (w 0)
base-rB {S} (hΩ κ g) v w = base-rB (g (bot S κ)) v (w (bot S κ))

rsAll : W supD → J supD → V supD → W supD
rsAll w j v c = rB c v (w c)

diag-raise : Raise supD
diag-raise = record
  { rs = rsAll
  ; set = λ {w} {j} {j′} v e k → base-rB j′ v (w j′)
  ; keep = λ v e nk → ⊥-elim (nk e) }

-- 它把一切成员的读数都改成 v (不是 "升一份留别份")
diag-moves : ∀ w j j′ v → obs supD j′ (rs diag-raise w j v) ≡ v
diag-moves w j j′ v = base-rB j′ v (w j′)

-- 同一个世界/成员/键/读数: 定义域恒真推出分离子, 定义域只含同一成员时有实例
bare-vs-diag : (Raise TR.supF → Sep) × Raise supD
bare-vs-diag = TR.sup-bare→Sep , diag-raise
```

## §3 单一读数类型: 框架装不下跨级的成员

`Fac F j X`: 成员 $j$ 的读数经 $X$ 分解, 嵌入 `eX` 有左逆 `dX`.

```agda
record Fac (F : RaiseFrame) (j : J F) (X : Set) : Set where
  field
    tX : W F → X
    eX : X → V F
    dX : V F → X
    de : ∀ x → dX (eX x) ≡ x
    ob : ∀ w → obs F j w ≡ eX (tX w)
open Fac public

fac-id : ∀ F j → Fac F j (V F)
fac-id F j = record { tX = obs F j ; eX = λ x → x ; dX = λ x → x ; de = λ x → refl ; ob = λ w → refl }

module _ {F : RaiseFrame} (R : Raise F) where
  -- 定义域含 (j , j) 的成员的读数取遍 V
  raise-onto : ∀ {w j} → Ev F w j j → ∀ v → Σ (W F) (λ w′ → obs F j w′ ≡ v)
  raise-onto {w} {j} ev v = rs R w j v , set R v ev refl

  raise-iso : ∀ {w j X} → Ev F w j j → (Φ : Fac F j X) → ∀ v → eX Φ (dX Φ v) ≡ v
  raise-iso {w} {j} ev Φ v =
    trans (cong (λ y → eX Φ (dX Φ y)) q) (trans (cong (eX Φ) (de Φ (tX Φ r))) (sym q))
    where
    r = rs R w j v
    q : v ≡ eX Φ (tX Φ r)
    q = trans (sym (set R v ev refl)) (ob Φ r)

  raise-adj : ∀ {w w′ jL jH} → Ev F w jL jL → Ev F w′ jH jH →
    ∀ {S′ : KS} (κ : K S′) → Fac F jL (E S′ κ) → Fac F jH (HB S′) → ⊥
  raise-adj evL evH κ ΦL ΦH =
    no-retract κ (λ x → dX ΦL (eX ΦH x)) (λ y → dX ΦH (eX ΦL y))
      (λ x → trans (cong (dX ΦH) (raise-iso evL ΦL (eX ΦH x))) (de ΦH x))

  -- 读数带标签: 定义域含 (j , j) 时标签不能固定
  raise-tag : ∀ {w j} {T : Set} (tag : V F → T) {t₀ : T} → Ev F w j j →
    (∀ w′ → tag (obs F j w′) ≡ t₀) → ∀ v → tag v ≡ t₀
  raise-tag tag ev fx v with raise-onto ev v
  ... | w′ , e = trans (cong tag (sym e)) (fx w′)

-- 实例: SL 的第 0 层与第 1 层的新种类 (坐标 HB (Lv lz), HB (Lv (ls lz)) = HB (step (Lv lz)))
no-frame-SL01 : ∀ {F} (R : Raise F) {w w′ jL jH} → Ev F w jL jL → Ev F w′ jH jH →
  Fac F jL (HB (Lv lz)) → Fac F jH (HB (Lv (ls lz))) → ⊥
no-frame-SL01 R evL evH ΦL ΦH = raise-adj R evL evH {S′ = Lv (ls lz)} (inj₂ tt) ΦL ΦH
```

**前提实例.** 构造一路的 `Pos` 框架, 读数类型取 `HB (Lv lz)` 或 `HB (Lv (ls lz))`: 各有合法升界 (`TR.Pos.posR`), 定义域恒真 (含自身对), 读数经 $X=V$ 分解. 所以 `raise-adj` 的前提各半可满足.

```agda
FL0 : RaiseFrame
FL0 = TR.Pos.posF {S₀} {azero} {hz} tt tt (HB (Lv lz))

FL1 : RaiseFrame
FL1 = TR.Pos.posF {S₀} {azero} {hz} tt tt (HB (Lv (ls lz)))

j₀ : TR.Pos.PJ {S₀} {azero} {hz} tt tt ℕ
j₀ = hz , hself

facL : Raise FL0 × Ev FL0 (λ _ _ → hz) (hz , hself) (hz , hself) × Fac FL0 (hz , hself) (HB (Lv lz))
facL = TR.Pos.posR tt tt (HB (Lv lz)) , tt , fac-id FL0 (hz , hself)

facH : Raise FL1 × Ev FL1 (λ _ _ → hz) (hz , hself) (hz , hself) × Fac FL1 (hz , hself) (HB (Lv (ls lz)))
facH = TR.Pos.posR tt tt (HB (Lv (ls lz))) , tt , fac-id FL1 (hz , hself)
```

## §4 `Raise` 不要求世界变大

构造一路的实例框架 (`posInst` 的框架, 读数 $\mathbb N$): 世界 $w_1$ 处处读 $1$; **任一**合法升界把成员 $j_0$ 置成 $0$ 后读 $0$.

```agda
F₀ : RaiseFrame
F₀ = TR.Pos.posF {S₀} {azero} {hz} tt tt ℕ

w1 : W F₀
w1 _ _ = 1

posSelf : Ev F₀ w1 j₀ j₀
posSelf = tt

any-lowers : ∀ (R : Raise F₀) → (obs F₀ j₀ (rs R w1 j₀ 0) ≡ 0) × (obs F₀ j₀ w1 ≡ 1)
any-lowers R = set R 0 posSelf refl , refl

-- 构造一路的实例本身
posInst-lowers : obs F₀ j₀ (rs TR.posInst w1 j₀ 0) ≡ 0
posInst-lowers = proj₁ (any-lowers TR.posInst)
```

## §5 结论 (按档)

- **[定理, 盲]** **`shrink`**, `empty-raise` (`Raise` 对定义域向下封闭); **`diag-raise`**, **`diag-moves`**, **`bare-vs-diag`** (`Lev` 的裸坐标积世界: 只改定义域, 从 "推出分离子" 变成 "有实例, 且一起升"); **`any-lowers`**, `posInst-lowers` (`Raise` 没有世界变大的律).
- **[定理, 边界]** `raise-onto`, **`raise-iso`**, **`raise-adj`**, **`no-frame-SL01`**, **`raise-tag`** (单一读数类型的框架装不下跨级成员).
- **[定理, 前提实例]** `fac-id`, `facL`, `facH`, `posSelf`.
- **[判断]** (1) `Raise` 与 `LvCrit` 同型: 判据定死的是 "定义域里的读数", 定义域本身由候选选; `Ev` 越小越容易满足 (`shrink`), 所以要从判据推出 "Ω-并只取有界坐标", 还要一条向上封闭的要求: 定义域必须含哪些异键对 (例如 "同一合法界之下的一切位置对"). (2) 跨级 (C6 的核心: 各级新种类各自升界) 不能放进一个单一读数的框架 (`raise-adj`); 要么每级一个框架 (那时级之间的升界关系不受 `Raise` 约束), 要么读数类型随成员变 (接口没有这种框架; `TreeLangRaise` 文件头 (ii) 指出它要沿相等证明搬运). (3) 穷尽是判断.
