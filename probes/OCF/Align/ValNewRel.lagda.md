# 新闭项的值 (一): 带 "多出一段" 的互模拟

> 不含记号. 入口 [ValNew](ValNew.lagda.md). 第 4 层: 只新增关系与定理, 不改树, 折叠, 合法性. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用函数外延, 不用 UIP 作前提.
>
> 本篇对一切种类结构 $T$ (层在 `HB (step T)`, 数据是 [GenFoldIf](GenFoldIf.lagda.md) 的 `DataG`) 定义一个数据之间的关系 `Mo` ("左边被右边模拟, 右边可以多出一段"):
>
> - **同形的部分** (`m1`, `m⨾`, `ml`, `mw`, `mi`, `mc`): 与 [TpPortSim](TpPortSim.lagda.md) 的互模拟 `SimD` 同形. 结点 `ni` 两边的结点证据 $R$, $R'$ 可以不同 (两个实例的 `cmpB` 给出的位置可以不同), 分支在相关的坐标上相关. 新增 `mc`: **旧种类** (`inj₁ κ`) 的闭包结点同形, 分支对一切更大的世界相关. 新种类 (`inj₂`) 的闭包结点**没有**构造子.
> - **多出的部分** (`mz`, `mr`, `me`, `ml0`): $0\preceq y$; $x\preceq y\Rightarrow x\preceq y⨾e$ (右边多一段); $x\preceq y\Rightarrow x\preceq e⨾y$ (左边多一段); $x\preceq d_0\Rightarrow x\preceq \mathrm{nl}\,d$ (取极限的第 0 项).
>
> 第 0 层上它推出 `sum` 的 $\le$ (`sum-M`, 定理). 关系对 `drp` (`drp-M`), 输入改写 `Int` (`Int-M`), 前缀 `Pre` (`Pre-M`) 保持; 层 $t$ 不含新种类的 $\Omega$-结点 (`NI t`) 时 $\Omega_t$ 与自己相关 (`Ωd-M`). 折叠对它的保持在 [ValNewRun](ValNewRun.lagda.md).
>
> **律的定义域.** 关系只比较同一层, 同一个世界上的两棵数据树; 不比较两个下标, 不判定种类相等 (`mc` 的两边是同一个种类, 字面相同). 判断: 不碰壁垒.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.ValNewRel where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst₂)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim)
open import OCF.Align.TLRuleSpec using (s≤; ≤l; l≤; ≤-refl; ≤-trans; ⊲→≤) renaming (_≤_ to _≤ᴬ_)
open import OCF.Align.HtTowerTy
open import OCF.Align.GenFoldIf
open import OCF.Align.GenFoldTree
```

## §1 层里没有新种类的 $\Omega$-结点

`NI h`: 层 $h\in$ `HB (step T)` 的 $\Omega$-结点都是旧种类 (`inj₁`). 沿第一位置向下封闭; `up` 的像与 `⊞` 保持它. 最终坍缩的层 $1\boxplus\mathrm{up}\,x$ 都满足它.

```agda
module _ {T : KS} where
  NI : HB (step T) → Set
  NI hz = ⊤
  NI (hs b) = NI b
  NI (hl f) = ∀ n → NI (f n)
  NI (hΩ (inj₁ _) g) = ∀ c → NI (g c)
  NI (hΩ (inj₂ _) g) = ⊥

  NI-⊲ : ∀ {a b w} → a ⊲[ w ] b → NI b → NI a
  NI-⊲ hself nb = nb
  NI-⊲ (hsuc p) nb = NI-⊲ p nb
  NI-⊲ (hlim n p) nb = NI-⊲ p (nb n)
  NI-⊲ (hLim {κ = inj₁ _} e p) nb = NI-⊲ p (nb _)
  NI-⊲ (hLim {κ = inj₂ _} e p) ()

  NI-up : ∀ (x : HB T) → NI (up x)
  NI-up hz = tt
  NI-up (hs x) = NI-up x
  NI-up (hl f) = λ n → NI-up (f n)
  NI-up (hΩ κ g) = λ c → NI-up (g c)

  NI-⊞ : ∀ a b → NI a → NI b → NI (a ⊞ b)
  NI-⊞ a hz na nb = na
  NI-⊞ a (hs b) na nb = NI-⊞ a b na nb
  NI-⊞ a (hl f) na nb = λ n → NI-⊞ a (f n) na (nb n)
  NI-⊞ a (hΩ (inj₁ κ) g) na nb = λ c → NI-⊞ a (g c) na (nb c)
  NI-⊞ a (hΩ (inj₂ _) g) na ()
```

## §2 关系

```agda
module Rel (T : KS) where
  open Tree T

  accK : ∀ {W k L} → StH {L₀} W k L → AccY k
  accK (ss P) = accC _ P
  accK (sl n P) = accC _ P
  accK (sL e P) = accC _ P

  -- 构造子形的可达证明 (GenFoldTree.accᴸ 对变量层不化成 acc)
  acc⁺ : ∀ {L} → AccY {L₀} L
  acc⁺ = acc accK

  module _ {L : HB L₀} (Lo : ∀ {W k} → StH W k L → ∀ {u} → D k u → D k u → Set) where
    data Mo : ∀ {W} → D L W → D L W → Set where
      m1  : ∀ {W} → Mo (n1 {W = W}) n1
      m⨾  : ∀ {W} {x x′ y y′ : D L W} → Mo x x′ → Mo y y′ → Mo (x ⨾ y) (x′ ⨾ y′)
      ml  : ∀ {W} {d d′ : ℕ → D L W} → (∀ n → Mo (d n) (d′ n)) → Mo (nl d) (nl d′)
      mi  : ∀ {W k} {R R′ : StH W k L}
              {v : ∀ {W′} → W ≤ W′ → LgW L₀ W′ → Vs L R W′ → D L W′}
              {v′ : ∀ {W′} → W ≤ W′ → LgW L₀ W′ → Vs L R′ W′ → D L W′} →
            (∀ {W′} (p : W ≤ W′) (l : LgW L₀ W′) y y′ → Lo R (outS R y) (outS R′ y′) → Mo (v p l y) (v′ p l y′)) →
            Mo (ni R v) (ni R′ v′)
      mc  : ∀ {W κ} {z z′ : ZK T L (inj₁ κ)} {v v′ : ∀ {W′} → W ≤ W′ → LgW L₀ W′ → D L W′} →
            (∀ {W′} (p : W ≤ W′) (l : LgW L₀ W′) → Mo (v p l) (v′ p l)) → Mo (nc (inj₁ κ) z v) (nc (inj₁ κ) z′ v′)
      mw  : ∀ {W₀ W} {p : W₀ ≤ W} {x x′ : D L W₀} → Mo x x′ → Mo (nw p x) (nw p x′)
      mz  : ∀ {W} {y : D L W} → Mo n0 y
      mr  : ∀ {W} {x y e : D L W} → Mo x y → Mo x (y ⨾ e)
      me  : ∀ {W} {x y e : D L W} → Mo x y → Mo x (e ⨾ y)
      ml0 : ∀ {W} {x : D L W} {d : ℕ → D L W} → Mo x (d 0) → Mo x (nl d)

  RelA : ∀ {L} → AccY L → ∀ {W} → D L W → D L W → Set
  RelA (acc g) = Mo (λ R → RelA (g R))

  Rl : ∀ L {W} → D L W → D L W → Set
  Rl L = RelA (acc⁺ {L})

  irr : ∀ {L} (a b : AccY L) {W} {x y : D L W} → RelA a x y → RelA b x y
  irr (acc f) (acc g) m1 = m1
  irr (acc f) (acc g) (m⨾ p q) = m⨾ (irr (acc f) (acc g) p) (irr (acc f) (acc g) q)
  irr (acc f) (acc g) (ml h) = ml (λ n → irr (acc f) (acc g) (h n))
  irr (acc f) (acc g) (mi {R = R} h) = mi (λ p l y y′ r → irr (acc f) (acc g) (h p l y y′ (irr (g R) (f R) r)))
  irr (acc f) (acc g) (mc h) = mc (λ p l → irr (acc f) (acc g) (h p l))
  irr (acc f) (acc g) (mw p) = mw (irr (acc f) (acc g) p)
  irr (acc f) (acc g) mz = mz
  irr (acc f) (acc g) (mr p) = mr (irr (acc f) (acc g) p)
  irr (acc f) (acc g) (me p) = me (irr (acc f) (acc g) p)
  irr (acc f) (acc g) (ml0 p) = ml0 (irr (acc f) (acc g) p)

  toRl : ∀ {L} (a : AccY L) {W} {x y : D L W} → RelA a x y → Rl L x y
  toRl a = irr a acc⁺

  ofRl : ∀ {L} (a : AccY L) {W} {x y : D L W} → Rl L x y → RelA a x y
  ofRl a = irr acc⁺ a
```

## §3 第 0 层: 关系推出 `sum` 的 $\le$

```agda
  sum≥ : ∀ {W} b (x : D₀ W) → b ≤ᴬ sum b x
  sum≥ b x = ⊲→≤ (sum-fst b x)

  pt≥ : ∀ {W} b (d : ℕ → D₀ W) n → b ≤ᴬ pt b d n
  pt≥ b d zero = ≤-refl b
  pt≥ b d (suc n) = ≤-trans (pt≥ b d n) (sum≥ (pt b d n) (d n))

  sum-M : ∀ (a : AccY hz) {W} {x y : D₀ W} → RelA a x y → ∀ {b b′} → b ≤ᴬ b′ → sum b x ≤ᴬ sum b′ y
  pt-M  : ∀ (a : AccY hz) {W} {d d′ : ℕ → D₀ W} → (∀ n → RelA a (d n) (d′ n)) → ∀ {b b′} → b ≤ᴬ b′ → ∀ n → pt b d n ≤ᴬ pt b′ d′ n
  sum-M (acc g) m1 h = s≤ h
  sum-M (acc g) (m⨾ p q) h = sum-M (acc g) q (sum-M (acc g) p h)
  sum-M (acc g) (ml hd) h = l≤ (λ n → ≤l n (pt-M (acc g) hd h n))
  sum-M (acc g) (mi {R = ()} _) h
  sum-M (acc g) (mc {z = ()} _) h
  sum-M (acc g) (mw p) h = sum-M (acc g) p h
  sum-M (acc g) {y = y} mz h = ≤-trans h (sum≥ _ y)
  sum-M (acc g) (mr {e = e} p) h = ≤-trans (sum-M (acc g) p h) (sum≥ _ e)
  sum-M (acc g) (me {e = e} p) h = sum-M (acc g) p (≤-trans h (sum≥ _ e))
  sum-M (acc g) (ml0 p) h = ≤l 1 (sum-M (acc g) p h)
  pt-M a hd h zero = h
  pt-M a hd h (suc n) = sum-M a (hd n) (pt-M a hd h n)

  drp-M : ∀ (a a′ : AccY hz) {W W′} {x y : D₀ W} → RelA a x y → RelA a′ (drp {W} {W′} x) (drp {W} {W′} y)
  drp-M (acc g) (acc g′) m1 = m1
  drp-M (acc g) (acc g′) (m⨾ p q) = m⨾ (drp-M (acc g) (acc g′) p) (drp-M (acc g) (acc g′) q)
  drp-M (acc g) (acc g′) (ml h) = ml (λ n → drp-M (acc g) (acc g′) (h n))
  drp-M (acc g) (acc g′) (mi {R = ()} _)
  drp-M (acc g) (acc g′) (mc {z = ()} _)
  drp-M (acc g) (acc g′) (mw p) = drp-M (acc g) (acc g′) p
  drp-M (acc g) (acc g′) mz = mz
  drp-M (acc g) (acc g′) (mr p) = mr (drp-M (acc g) (acc g′) p)
  drp-M (acc g) (acc g′) (me p) = me (drp-M (acc g) (acc g′) p)
  drp-M (acc g) (acc g′) (ml0 p) = ml0 (drp-M (acc g) (acc g′) p)
```

## §4 $\Omega_t$ 与自己相关; 结点证据的搬运

```agda
  module OmM (tp : TopG L₀) where
    open Om tp

    Ωd-M : ∀ t → NI t → (a : AccY t) → ∀ {W} → RelA a (Ωd t {W}) (Ωd t {W})
    Ωd-M hz nt (acc g) = m1
    Ωd-M (hs b) nt (acc g) = m⨾ m1 (mi (λ p l y y′ r → m1))
    Ωd-M (hl f) nt (acc g) = m⨾ m1 (ml (λ n → mi (λ p l y y′ r → m1)))
    Ωd-M (hΩ (inj₁ κ) h) nt (acc g) = m⨾ m1 (mc (λ p l → mi (λ p′ l′ y y′ r → m1)))
    Ωd-M (hΩ (inj₂ _) h) () a

  outC-inC : ∀ {b W a u} (P : a ⊲[ W ] b) (x : D a u) → outC P (inC P x) ≡ x
  outC-inC hself x = refl
  outC-inC (hsuc P) x = outC-inC P x
  outC-inC (hlim n P) x = outC-inC P x
  outC-inC (hLim e P) x = outC-inC P x

  outS-inS : ∀ {L W k u} (R : StH W k L) (x : D k u) → outS R (inS R x) ≡ x
  outS-inS (ss P) x = outC-inC P x
  outS-inS (sl n P) x = outC-inC P x
  outS-inS (sL e P) x = outC-inC P x

  conv : ∀ {L W k u} (a : AccY k) (R R′ : StH W k L) {x y : D k u} → Rl k x y → RelA a (outS R (inS R x)) (outS R′ (inS R′ y))
  conv a R R′ {x} {y} r = subst₂ (RelA a) (sym (outS-inS R x)) (sym (outS-inS R′ y)) (ofRl a r)
```

## §5 前缀与输入改写

```agda
  Pre-M : ∀ {L : HB L₀} {W₀ W} (q₀ : W₀ ≤ W) {d₁ d₂ : ℕ → D L W₀} → (∀ n → Rl L (d₁ n) (d₂ n)) → ∀ n → Rl L (Pre q₀ d₁ n) (Pre q₀ d₂ n)
  Pre-M q₀ h zero = mz
  Pre-M q₀ h (suc n) = m⨾ (Pre-M q₀ h n) (mw (h n))

  UR : ∀ (k ly : HB L₀) (W : Wd L₀) → (∀ {W′} → W ≤ W′ → LgW L₀ W′ → D k W′ → D ly W′) → (∀ {W′} → W ≤ W′ → LgW L₀ W′ → D k W′ → D ly W′) → Set
  UR k ly W u₁ u₂ = ∀ {W′} (p : W ≤ W′) (l : LgW L₀ W′) {y₁ y₂ : D k W′} → Rl k y₁ y₂ → Rl ly (u₁ p l y₁) (u₂ p l y₂)

  Int-M : ∀ {ly k W₀ W} (a₁ a₂ : AccY k) {x₁ x₂ : D k W₀} → Rl k x₁ x₂ → (q₀ : W₀ ≤ W) (lW : LgW L₀ W)
          (zy₁ zy₂ : ∀ κ → ZK T k κ → ZK T ly κ)
          (mk₁ mk₂ : ∀ {W₁ j} → W ≤ W₁ → StH W₁ j k → StH W₁ j ly) {u₁ u₂ : ∀ {W′} → W ≤ W′ → LgW L₀ W′ → D k W′ → D ly W′} → UR k ly W u₁ u₂ →
          {w₁ w₂ : D k W} → Rl k w₁ w₂ → Rl ly (Int a₁ x₁ q₀ lW zy₁ mk₁ u₁ w₁) (Int a₂ x₂ q₀ lW zy₂ mk₂ u₂ w₂)
  Int-M a₁ a₂ m1 q₀ lW zy₁ zy₂ mk₁ mk₂ hu hw = hu ≤rf lW hw
  Int-M a₁ a₂ (m⨾ hx hy) q₀ lW zy₁ zy₂ mk₁ mk₂ hu hw =
    m⨾ (Int-M a₁ a₂ hx q₀ lW zy₁ zy₂ mk₁ mk₂ hu hw) (Int-M a₁ a₂ hy q₀ lW zy₁ zy₂ mk₁ mk₂ hu (m⨾ hw (mw hx)))
  Int-M a₁ a₂ (ml h) q₀ lW zy₁ zy₂ mk₁ mk₂ hu hw =
    ml (λ n → Int-M a₁ a₂ (h n) q₀ lW zy₁ zy₂ mk₁ mk₂ hu (m⨾ hw (Pre-M q₀ h n)))
  Int-M a₁ a₂ (mw {p = p} hx) q₀ lW zy₁ zy₂ mk₁ mk₂ hu hw = Int-M a₁ a₂ hx (≤tr p q₀) lW zy₁ zy₂ mk₁ mk₂ hu hw
  Int-M a₁ a₂ (mc h) q₀ lW zy₁ zy₂ mk₁ mk₂ hu hw =
    mc (λ p lW′ → Int-M a₁ a₂ (h (≤tr q₀ p) lW′) ≤rf lW′ zy₁ zy₂ (λ p′ → mk₁ (≤tr p p′)) (λ p′ → mk₂ (≤tr p p′)) (λ p′ → hu (≤tr p p′)) (mw hw))
  Int-M a₁ a₂ mz q₀ lW zy₁ zy₂ mk₁ mk₂ hu hw = mz
  Int-M a₁ a₂ (mr hx) q₀ lW zy₁ zy₂ mk₁ mk₂ hu hw = mr (Int-M a₁ a₂ hx q₀ lW zy₁ zy₂ mk₁ mk₂ hu hw)
  Int-M a₁ a₂ (me hx) q₀ lW zy₁ zy₂ mk₁ mk₂ hu hw = me (Int-M a₁ a₂ hx q₀ lW zy₁ zy₂ mk₁ mk₂ hu (mr hw))
  Int-M a₁ a₂ (ml0 hx) q₀ lW zy₁ zy₂ mk₁ mk₂ hu hw = ml0 (Int-M a₁ a₂ hx q₀ lW zy₁ zy₂ mk₁ mk₂ hu (mr hw))
  Int-M (acc g₁) (acc g₂) (mi {R = R₁} {R′ = R₂} h) q₀ lW zy₁ zy₂ mk₁ mk₂ hu hw =
    mi (λ p lW′ y₁ y₂ r →
      Int-M (acc g₁) (acc g₂)
        (h (≤tr q₀ p) lW′ _ _ (conv (accK R₁) R₁ R₂ (toRl (accK (mk₁ ≤rf (Kup {S = L₀} q₀ R₁))) r)))
        ≤rf lW′ zy₁ zy₂ (λ p′ → mk₁ (≤tr p p′)) (λ p′ → mk₂ (≤tr p p′)) (λ p′ → hu (≤tr p p′))
        (m⨾ (mw hw) (Int-M (g₁ R₁) (g₂ R₂) (toRl (accK (mk₁ ≤rf (Kup {S = L₀} q₀ R₁))) r) ≤rf lW′ (zkS {T} R₁) (zkS {T} R₂)
                       (mkOf R₁ (≤tr q₀ p)) (mkOf R₂ (≤tr q₀ p))
                       (λ p′ l′ r′ → h (≤tr (≤tr q₀ p) p′) l′ _ _ (conv (accK R₁) R₁ R₂ r′)) mz)))
```
