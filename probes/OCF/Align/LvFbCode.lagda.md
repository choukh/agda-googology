# 层号由回灌给出 (W2): 下标用路径码, 码的相等可判定

> 不含记号. 入口 [LvFb](LvFb.lagda.md). 作者选定原话: "A3 提前探路". 本篇是三种不需要外延的写法里的第二种 (W2): 世界的分量不以坐标 $c$ (或 (坐标, 证据) 对 $(c,p)$) 为下标, 而以**路径码**为下标. 码是一个不带索引的数据类型 (从外层界 $b$ 往下走的每一步: 停, 进后继, 进第 $n$ 个分支, 进 `A`-坐标的分支, `A`-坐标自己也用码), 合法的码由一个对 $b$ 递归算出的命题 `vB` 刻画. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延, 不用 UIP 作前提.
>
> **结论 (全部是定理).**
>
> 1. **码的相等可判定** (`≟RB`, `≟RA`, `code-≟`), 所以码上有 UIP (`code-uip`, 标准库的 Hedberg `Decidable⇒UIP`, 不用 K). 合法性 `vB a b r` 是命题 (`vB-prop`).
> 2. **码覆盖一切可入坐标** (`cd`, `cd-tgt`): 每个证据 $p : c\lhd_{[a]} b$ 给出一个码, 码的目标就是 $c$; 每个码给出一个证据 (`pB`).
> 3. **单个增量的更新在一切码上有精确的 `at` 律** (`CW.raiseC`, `CW.at`, `CW.off`, `CW.mono`, `CW.legal`). 更新在 $k_0$ 处接上 $\delta$, 别的码不动; 判定只比较两个码 (都在同一个外层界 $b$ 之下). `at` 的证明沿码的相等搬运, 码上的环由 UIP 是 `refl`; **不要 `LoopFix`, 不要族增量**. 对照: 以 $(c,p)$ 为下标时, 单个增量的 `at` 与保相干要 $c$ 上的环搬运平凡 (`NegColimALoop.raise1→fix₀`, `LocUipNegLoop`), 族增量在 $\omega$ 处要 `Uniform` (`NegFamSec.uniformAll→fix`).
> 4. **在极限坐标 $\omega$ 的码上** (外层界 $\omega+1$): `atω` 是定义相等 (`refl`), 也是第 3 条的实例.
> 5. **代价: 拷贝.** 同一坐标有不同的码 (`copy-tgt`: 外层界 $\omega+1$ 之下 $2$ 有两个码), 更新只升一个 (`copy-split`). 这与 `AdmEvNeg.no-indep₀` 同一现象: 种类必须带证据. 若要把同一坐标的拷贝一起升 (按坐标判定), 搬运就沿坐标的相等, 回到环的问题 (判断, 未写成定理; 依据 `NegColimALoop.raise1→fix₀` 的形状).
>
> **对律的定义域.** 每一条律里的每一对下标都是同一外层世界 $(a,b)$ 之下的码 (`Code a b`), 公共上界是 $b$; `off` 是对可入下标 (码) 的律, 不是对裸坐标的律.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LvFbCode where

open import Data.Nat using (ℕ; zero; suc)
import Data.Nat as N
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong; cong₂)
open import Axiom.UniquenessOfIdentityProofs using (module Decidable⇒UIP)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtTowerTy
open import OCF.Align.AdmWCoh using (fin; ω₀; lg-fin; Lg-ω₀)
```

## §1 `A` 的码

```agda
data RA : Set where
  aH : RA
  aP : RA → RA
  aL : ℕ → RA → RA

vA  : A → RA → Set
vAP : A → RA → Set
vAL : A → ℕ → RA → Set
vA a aH = ⊤
vA a (aP r) = vAP a r
vA a (aL n r) = vAL a n r
vAP (asuc a) r = vA a r
vAP azero r = ⊥
vAP (alim f) r = ⊥
vAL (alim f) n r = vA (f n) r
vAL azero n r = ⊥
vAL (asuc a) n r = ⊥

tA  : (a : A) (r : RA) → vA a r → A
tAP : (a : A) (r : RA) → vAP a r → A
tAL : (a : A) (n : ℕ) (r : RA) → vAL a n r → A
tA a aH _ = a
tA a (aP r) v = tAP a r v
tA a (aL n r) v = tAL a n r v
tAP (asuc a) r v = tA a r v
tAL (alim f) n r v = tA (f n) r v

pA  : (a : A) (r : RA) (v : vA a r) → tA a r v ⊲ a
pAP : (a : A) (r : RA) (v : vAP a r) → tAP a r v ⊲ a
pAL : (a : A) (n : ℕ) (r : RA) (v : vAL a n r) → tAL a n r v ⊲ a
pA a aH _ = C.self
pA a (aP r) v = pAP a r v
pA a (aL n r) v = pAL a n r v
pAP (asuc a) r v = C.suc (pA a r v)
pAL (alim f) n r v = C.lim n (pA (f n) r v)

vA-prop  : ∀ a r (x y : vA a r) → x ≡ y
vAP-prop : ∀ a r (x y : vAP a r) → x ≡ y
vAL-prop : ∀ a n r (x y : vAL a n r) → x ≡ y
vA-prop a aH x y = refl
vA-prop a (aP r) x y = vAP-prop a r x y
vA-prop a (aL n r) x y = vAL-prop a n r x y
vAP-prop (asuc a) r x y = vA-prop a r x y
vAL-prop (alim f) n r x y = vA-prop (f n) r x y

-- 证据给码
cdA : ∀ {c a} → c ⊲ a → RA
cdA C.self = aH
cdA (C.suc p) = aP (cdA p)
cdA (C.lim n p) = aL n (cdA p)

vcdA : ∀ {c a} (p : c ⊲ a) → vA a (cdA p)
vcdA C.self = tt
vcdA (C.suc p) = vcdA p
vcdA (C.lim n p) = vcdA p

tcdA : ∀ {c a} (p : c ⊲ a) → tA a (cdA p) (vcdA p) ≡ c
tcdA C.self = refl
tcdA (C.suc p) = tcdA p
tcdA (C.lim n p) = tcdA p
```

## §2 高度的码

外层世界 $(a, b)$: `A`-层 $a$ (Ω-节点的坐标在 $a$ 之下), 高度界 $b$.

```agda
data RB : Set where
  bH : RB
  bP : RB → RB
  bL : ℕ → RB → RB
  bΩ : RA → RB → RB

vB  : A → HB S₀ → RB → Set
vBP : A → HB S₀ → RB → Set
vBL : A → HB S₀ → ℕ → RB → Set
vBΩ : A → HB S₀ → RA → RB → Set
vB a b bH = ⊤
vB a b (bP r) = vBP a b r
vB a b (bL n r) = vBL a b n r
vB a b (bΩ ra r) = vBΩ a b ra r
vBP a (hs b) r = vB a b r
vBP a hz r = ⊥
vBP a (hl f) r = ⊥
vBP a (hΩ κ g) r = ⊥
vBL a (hl f) n r = vB a (f n) r
vBL a hz n r = ⊥
vBL a (hs b) n r = ⊥
vBL a (hΩ κ g) n r = ⊥
vBΩ a (hΩ κ g) ra r = Σ (vA a ra) (λ va → vB a (g (tA a ra va)) r)
vBΩ a hz ra r = ⊥
vBΩ a (hs b) ra r = ⊥
vBΩ a (hl f) ra r = ⊥

tB  : (a : A) (b : HB S₀) (r : RB) → vB a b r → HB S₀
tBP : (a : A) (b : HB S₀) (r : RB) → vBP a b r → HB S₀
tBL : (a : A) (b : HB S₀) (n : ℕ) (r : RB) → vBL a b n r → HB S₀
tBΩ : (a : A) (b : HB S₀) (ra : RA) (r : RB) → vBΩ a b ra r → HB S₀
tB a b bH _ = b
tB a b (bP r) v = tBP a b r v
tB a b (bL n r) v = tBL a b n r v
tB a b (bΩ ra r) v = tBΩ a b ra r v
tBP a (hs b) r v = tB a b r v
tBL a (hl f) n r v = tB a (f n) r v
tBΩ a (hΩ κ g) ra r (va , v) = tB a (g (tA a ra va)) r v

pB  : (a : A) (b : HB S₀) (r : RB) (v : vB a b r) → tB a b r v ⊲[ a ] b
pBP : (a : A) (b : HB S₀) (r : RB) (v : vBP a b r) → tBP a b r v ⊲[ a ] b
pBL : (a : A) (b : HB S₀) (n : ℕ) (r : RB) (v : vBL a b n r) → tBL a b n r v ⊲[ a ] b
pBΩ : (a : A) (b : HB S₀) (ra : RA) (r : RB) (v : vBΩ a b ra r) → tBΩ a b ra r v ⊲[ a ] b
pB a b bH _ = hself
pB a b (bP r) v = pBP a b r v
pB a b (bL n r) v = pBL a b n r v
pB a b (bΩ ra r) v = pBΩ a b ra r v
pBP a (hs b) r v = hsuc (pB a b r v)
pBL a (hl f) n r v = hlim n (pB a (f n) r v)
pBΩ a (hΩ κ g) ra r (va , v) = hLim (pA a ra va) (pB a (g (tA a ra va)) r v)

vB-prop  : ∀ a b r (x y : vB a b r) → x ≡ y
vBP-prop : ∀ a b r (x y : vBP a b r) → x ≡ y
vBL-prop : ∀ a b n r (x y : vBL a b n r) → x ≡ y
vBΩ-prop : ∀ a b ra r (x y : vBΩ a b ra r) → x ≡ y
vB-prop a b bH x y = refl
vB-prop a b (bP r) x y = vBP-prop a b r x y
vB-prop a b (bL n r) x y = vBL-prop a b n r x y
vB-prop a b (bΩ ra r) x y = vBΩ-prop a b ra r x y
vBP-prop a (hs b) r x y = vB-prop a b r x y
vBL-prop a (hl f) n r x y = vB-prop a (f n) r x y
vBΩ-prop a (hΩ κ g) ra r (va , v) (va′ , v′) with vA-prop a ra va va′
... | refl = cong (va ,_) (vB-prop a (g (tA a ra va)) r v v′)

Code : A → HB S₀ → Set
Code a b = Σ RB (vB a b)

tgt : ∀ {a b} → Code a b → HB S₀
tgt {a} {b} k = tB a b (proj₁ k) (proj₂ k)

pth : ∀ {a b} (k : Code a b) → tgt k ⊲[ a ] b
pth {a} {b} k = pB a b (proj₁ k) (proj₂ k)
```

## §3 码的相等可判定, 码上有 UIP

```agda
-- 尾部投影 (取单射用, 不对索引匹配)
tlA : RA → RA
tlA aH = aH
tlA (aP r) = r
tlA (aL n r) = r

tlB : RB → RB
tlB bH = bH
tlB (bP r) = r
tlB (bL n r) = r
tlB (bΩ ra r) = r

≟RA : (r s : RA) → Dec (r ≡ s)
≟RA aH aH = yes refl
≟RA aH (aP s) = no (λ ())
≟RA aH (aL m s) = no (λ ())
≟RA (aP r) aH = no (λ ())
≟RA (aP r) (aP s) with ≟RA r s
... | yes refl = yes refl
... | no ne = no (λ { refl → ne refl })
≟RA (aP r) (aL m s) = no (λ ())
≟RA (aL n r) aH = no (λ ())
≟RA (aL n r) (aP s) = no (λ ())
≟RA (aL n r) (aL m s) with n N.≟ m | ≟RA r s
... | yes refl | yes refl = yes refl
... | no ne | _ = no (λ { refl → ne refl })
... | yes refl | no ne = no (λ e → ne (cong tlA e))

≟RB : (r s : RB) → Dec (r ≡ s)
≟RB bH bH = yes refl
≟RB bH (bP s) = no (λ ())
≟RB bH (bL m s) = no (λ ())
≟RB bH (bΩ sa s) = no (λ ())
≟RB (bP r) bH = no (λ ())
≟RB (bP r) (bP s) with ≟RB r s
... | yes refl = yes refl
... | no ne = no (λ { refl → ne refl })
≟RB (bP r) (bL m s) = no (λ ())
≟RB (bP r) (bΩ sa s) = no (λ ())
≟RB (bL n r) bH = no (λ ())
≟RB (bL n r) (bP s) = no (λ ())
≟RB (bL n r) (bL m s) with n N.≟ m | ≟RB r s
... | yes refl | yes refl = yes refl
... | no ne | _ = no (λ { refl → ne refl })
... | yes refl | no ne = no (λ e → ne (cong tlB e))
≟RB (bL n r) (bΩ sa s) = no (λ ())
≟RB (bΩ ra r) bH = no (λ ())
≟RB (bΩ ra r) (bP s) = no (λ ())
≟RB (bΩ ra r) (bL m s) = no (λ ())
≟RB (bΩ ra r) (bΩ sa s) with ≟RA ra sa | ≟RB r s
... | yes refl | yes refl = yes refl
... | no ne | _ = no (λ { refl → ne refl })
... | yes refl | no ne = no (λ e → ne (cong tlB e))

code-≟ : ∀ {a b} (k k′ : Code a b) → Dec (k ≡ k′)
code-≟ {a} {b} (r , v) (s , u) with ≟RB r s
... | yes refl = yes (cong (r ,_) (vB-prop a b r v u))
... | no ne = no (λ e → ne (cong proj₁ e))

code-uip : ∀ {a b} {k k′ : Code a b} (e e′ : k ≡ k′) → e ≡ e′
code-uip {a} {b} = Decidable⇒UIP.≡-irrelevant (code-≟ {a} {b})
```

## §4 码覆盖一切可入坐标

```agda
infix 4 _⊲₀[_]_
_⊲₀[_]_ : HB S₀ → A → HB S₀ → Set
c ⊲₀[ a ] b = _⊲[_]_ {S₀} c a b

cdB : ∀ {a c b} → c ⊲₀[ a ] b → RB
cdB hself = bH
cdB (hsuc p) = bP (cdB p)
cdB (hlim n p) = bL n (cdB p)
cdB (hLim e p) = bΩ (cdA e) (cdB p)

vcdB : ∀ {a c b} (p : c ⊲₀[ a ] b) → vB a b (cdB p)
tcdB : ∀ {a c b} (p : c ⊲₀[ a ] b) → tB a b (cdB p) (vcdB p) ≡ c

-- 沿坐标的相等搬运合法性证明, 目标随之
private
  tB-sub : ∀ a (g : A → HB S₀) r {t x} (e : t ≡ x) (v : vB a (g x) r) →
           tB a (g t) r (subst (λ z → vB a (g z) r) (sym e) v) ≡ tB a (g x) r v
  tB-sub a g r refl v = refl

vcdB hself = tt
vcdB (hsuc p) = vcdB p
vcdB (hlim n p) = vcdB p
vcdB {a} (hLim {g = g} {c = x} e p) = vcdA e , subst (λ z → vB a (g z) (cdB p)) (sym (tcdA e)) (vcdB p)

tcdB hself = refl
tcdB (hsuc p) = tcdB p
tcdB (hlim n p) = tcdB p
tcdB {a} (hLim {g = g} {c = x} e p) = trans (tB-sub a g (cdB p) (tcdA e) (vcdB p)) (tcdB p)

cd : ∀ {a c b} → c ⊲₀[ a ] b → Code a b
cd p = cdB p , vcdB p

cd-tgt : ∀ {a c b} (p : c ⊲₀[ a ] b) → tgt (cd p) ≡ c
cd-tgt p = tcdB p
```

## §5 以码为下标的世界与单个增量的更新

分量族 $P$ 以码为下标 (实例里取 $P\,k$ = 坐标 `tgt k` 处的种类结构). 分量是 (世界, 槽).

```agda
module CW (a : A) (b : HB S₀) (P : Code a b → KS) where
  Cmpᶜ : Set
  Cmpᶜ = (k : Code a b) → Wd (P k) × HB (P k)

  slot : Cmpᶜ → (k : Code a b) → HB (P k)
  slot v k = proj₂ (v k)

  LgC : Cmpᶜ → Set
  LgC v = ∀ k → LgW (P k) (proj₁ (v k)) × LgB (proj₂ (v k))

  _≤C_ : Cmpᶜ → Cmpᶜ → Set
  v ≤C v′ = ∀ k → _≤w_ (P k) (proj₁ (v k)) (proj₁ (v′ k)) × (proj₂ (v k) ⊲[ proj₁ (v′ k) ] proj₂ (v′ k))

  module _ (k₀ : Code a b) (δ : HB (P k₀)) where
    tp : ∀ {k} → k₀ ≡ k → HB (P k)
    tp e = subst (λ j → HB (P j)) e δ

    upd : ∀ {k} → Dec (k₀ ≡ k) → Wd (P k) × HB (P k) → Wd (P k) × HB (P k)
    upd (yes e) x = proj₁ x , proj₂ x ⊞ tp e
    upd (no _) x = x

    upd-at : ∀ (d : Dec (k₀ ≡ k₀)) x → upd d x ≡ (proj₁ x , proj₂ x ⊞ δ)
    upd-at (yes e) x = cong (λ e′ → proj₁ x , proj₂ x ⊞ tp e′) (code-uip e refl)
    upd-at (no ne) x = ⊥-elim (ne refl)

    upd-off : ∀ {k} (d : Dec (k₀ ≡ k)) x → ¬ (k₀ ≡ k) → upd d x ≡ x
    upd-off (yes e) x ne = ⊥-elim (ne e)
    upd-off (no _) x ne = refl

    upd-≤ : ∀ {k} (d : Dec (k₀ ≡ k)) x → _≤w_ (P k) (proj₁ x) (proj₁ (upd d x)) × (proj₂ x ⊲[ proj₁ (upd d x) ] proj₂ (upd d x))
    upd-≤ {k} (yes e) x = ≤w-rf (P k) , ⊞-fst (proj₂ x) (tp e)
    upd-≤ {k} (no _) x = ≤w-rf (P k) , hself

    lg-tp : ∀ {k} (e : k₀ ≡ k) → LgB δ → LgB (tp e)
    lg-tp refl l = l

    upd-lg : ∀ {k} (d : Dec (k₀ ≡ k)) x → LgB δ → LgW (P k) (proj₁ x) × LgB (proj₂ x) →
             LgW (P k) (proj₁ (upd d x)) × LgB (proj₂ (upd d x))
    upd-lg (yes e) x lδ (lw , ls) = lw , Lg-⊞ (proj₂ x) (tp e) ls (lg-tp e lδ)
    upd-lg (no _) x lδ l = l

  raiseC : Cmpᶜ → (k₀ : Code a b) → HB (P k₀) → Cmpᶜ
  raiseC v k₀ δ k = upd k₀ δ (code-≟ k₀ k) (v k)

  -- 在 k₀ 处恰好接上 δ, 对一切码 (含极限坐标的码)
  at : ∀ v k₀ δ → raiseC v k₀ δ k₀ ≡ (proj₁ (v k₀) , slot v k₀ ⊞ δ)
  at v k₀ δ = upd-at k₀ δ (code-≟ k₀ k₀) (v k₀)

  -- 别的码不动 (两个码在同一外层界 b 之下)
  off : ∀ v k₀ δ k → ¬ (k₀ ≡ k) → raiseC v k₀ δ k ≡ v k
  off v k₀ δ k ne = upd-off k₀ δ (code-≟ k₀ k) (v k) ne

  mono : ∀ v k₀ δ → v ≤C raiseC v k₀ δ
  mono v k₀ δ k = upd-≤ k₀ δ (code-≟ k₀ k) (v k)

  legal : ∀ v k₀ δ → LgB δ → LgC v → LgC (raiseC v k₀ δ)
  legal v k₀ δ lδ lv k = upd-lg k₀ δ (code-≟ k₀ k) (v k) lδ (lv k)

  slot-at : ∀ v k₀ δ → slot (raiseC v k₀ δ) k₀ ≡ slot v k₀ ⊞ δ
  slot-at v k₀ δ = cong proj₂ (at v k₀ δ)
```

## §6 实例: 外层界 $\omega+1$, 在 $\omega$ 的码上升高

分量族: 码 $k$ 处取坐标 `tgt k` 的种类结构 `Lev (up (tgt k))` (`AdmWIf.G₀`). 起点世界: 一切分量取 `AdmWCoh.wz` 与槽 $0$.

```agda
open import OCF.Align.AdmWIf using (G₀)
open import OCF.Align.AdmWCoh using (wz; lg-wz)

bω : HB S₀
bω = hs ω₀

Pω : Code azero bω → KS
Pω k = G₀ (tgt k)

module Wω = CW azero bω Pω

v₀ : Wω.Cmpᶜ
v₀ k = wz (up (tgt k)) , hz

lv₀ : Wω.LgC v₀
lv₀ k = lg-wz (up (tgt k)) , tt

-- ω 的码与 n 的码
kω : Code azero bω
kω = bP bH , tt

kfin : ℕ → Code azero bω
kfin n = bP (bL n bH) , tt

tgt-kω : tgt kω ≡ ω₀
tgt-kω = refl

tgt-kfin : ∀ n → tgt (kfin n) ≡ fin n
tgt-kfin n = refl

-- ω 处的单个增量: 一个第 2 级新种类的节点 (坐标是 G₀ ω 的第 2 个分量的种类)
δω : HB (G₀ ω₀)
δω = hΩ (2 , inj₂ tt) (λ _ → hs hz)

lδω : LgB δω
lδω = (λ lw e e′ pr → hself) , (λ c lc → tt)

vω : Wω.Cmpᶜ
vω = Wω.raiseC v₀ kω δω

atω : Wω.slot vω kω ≡ hz ⊞ δω
atω = refl

atω′ : Wω.slot vω kω ≡ Wω.slot v₀ kω ⊞ δω
atω′ = Wω.slot-at v₀ kω δω

lvω : Wω.LgC vω
lvω = Wω.legal v₀ kω δω lδω lv₀

-- 拷贝: 2 有两个码, 只升其中一个
k2 k2′ : Code azero bω
k2 = kfin 2
k2′ = bP (bL 3 (bP bH)) , tt

copy-tgt : tgt k2 ≡ tgt k2′
copy-tgt = refl

copy-ne : ¬ (k2 ≡ k2′)
copy-ne ()

v₂ : Wω.Cmpᶜ
v₂ = Wω.raiseC v₀ k2 (hs hz)

copy-split : (Wω.slot v₂ k2 ≡ hs hz) × (Wω.slot v₂ k2′ ≡ hz)
copy-split = refl , refl
```

## §7 结论 (按档)

- **[定理]** `vA-prop`, `vB-prop`; **`≟RA`, `≟RB`, `code-≟`** (码的相等可判定); **`code-uip`** (码上 UIP, Hedberg).
- **[定理]** `pB`, `cd`, **`cd-tgt`**: 码与可入证据互相给出, 目标一致.
- **[定理]** **`CW.at`** (对一切码精确接长), `CW.off`, `CW.mono`, `CW.legal`, `CW.slot-at`.
- **[定理]** 实例: `atω` (`refl`), `atω′`, `lvω` (外层界 $\omega+1$, 在 $\omega$ 的码上的单个增量, 合法).
- **[定理]** `copy-tgt`, `copy-ne`, **`copy-split`**: 拷贝不随更新一致 (代价).
- **[判断]** 按坐标把拷贝一起升会回到环的搬运 (依据 `NegColimALoop.raise1→fix₀` 的形状; 没有写成定理).
- **[判断]** 原来带索引的证据类型 `c ⊲[a] b` 本身的相等是否可判定, 本篇不回答 (`cd` 不必是单射的证明要沿目标的相等, 那是环的问题); W2 用码代替它, 不需要回答.
