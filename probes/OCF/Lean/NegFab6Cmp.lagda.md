# NegFab6 (三): 与 CRw 的差

> 不含记号. 入口 [NegFab6](NegFab6.lagda.md). 验收文件: 导入 [CRw](CRw.lagda.md), 不在别的 `NegFab6*` 的导入闭包里. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.
>
> **这一篇证什么.** (1) `Fab6Cmp` 的 "逐项相同" 只是深度 4 的结点数相同; 这里的位置敏感指纹把 `TX`, `TU1`, `TU2` 分开 (`TX≢`, `TU1≢`, `TU2≢`, 是关于这三棵闭树不相等的定理, 不说哪棵大). (2) 同一个输入 $f+f$ ($f$ 是 $\Omega_1$ 层的地板): Fab6 的同底折叠结果是 `hE tt (φ f) g₀`, 分支原样, 外部结点恰好 2 个 (`NegFab6.atoms-f₂`); CRw 的结果是 $\Omega_1$-结点, 每个分支都被折过, 而且分支 $(1,d)$ 里的 $\Omega_1$-种类结点个数 (沿坐标 $c$ 走的度量 `cnt`) 不小于 $d$, 对一切可数树 $d$ (`crw-many`). 这是 "路径的效应" 的编译版: 前缀进分支, 逐分支折叠.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.NegFab6Cmp where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym)
import OCF.Lean.Fab6Base as N
open import OCF.Lean.Fab6 using (TX; TU1; TU2; topL)
open import OCF.Lean.NegFab6 using (φ; g₀)
import OCF.Lean.CRwBase as C
import OCF.Lean.CRw as R
open import OCF.Lean.CRwFold R.I₁ as F using (XS; gt; bX; sm; wf; mul; Σ⁺)
```

## §1 位置敏感的指纹 (有限计算)

`hN k x`: 深度 $k$ 的有界展开, 每个 ℕ-极限展开前 $k$ 项, 按位置加权. 这是计算, 盲区: 只看前 $k$ 项, 与序数大小无关.

```agda
hN : ℕ → N.Cd → ℕ
hsN : ℕ → ℕ → (ℕ → N.Cd) → ℕ
hN zero x = 0
hN (suc k) N.hz = 1
hN (suc k) (N.hs x) = 2 * hN (suc k) x + 1
hN (suc k) (N.hl f) = 3 + hsN k (suc k) f
hN (suc k) (N.hΩ () g)
hN (suc k) (N.hE () _ _)
hsN k zero f = 0
hsN k (suc i) f = (suc i) * hN k (f i) + hsN k i f

hC : ℕ → C.Cd → ℕ
hsC : ℕ → ℕ → (ℕ → C.Cd) → ℕ
hC zero x = 0
hC (suc k) C.hz = 1
hC (suc k) (C.hs x) = 2 * hC (suc k) x + 1
hC (suc k) (C.hl f) = 3 + hsC k (suc k) f
hC (suc k) (C.hΩ () g)
hsC k zero f = 0
hsC k (suc i) f = (suc i) * hC k (f i) + hsC k i f

cv : N.Cd → C.Cd
cv N.hz = C.hz
cv (N.hs x) = C.hs (cv x)
cv (N.hl f) = C.hl (λ n → cv (f n))
cv (N.hΩ () _)
cv (N.hE () _ _)

hX-N : hC 5 (cv TX) ≡ 11298
hX-N = refl

hX-C : hC 5 R.TX ≡ 11446
hX-C = refl

hU-N : hC 7 (cv TU1) ≡ 6643311
hU-N = refl

hU-C : hC 7 R.TU1 ≡ 6643319
hU-C = refl

h2-N : hC 8 (cv TU2) ≡ 232515889
h2-N = refl

h2-C : hC 8 R.TU2 ≡ 232515905
h2-C = refl

no₁ : ¬ (11298 ≡ 11446)
no₁ ()

no₂ : ¬ (6643311 ≡ 6643319)
no₂ ()

no₃ : ¬ (232515889 ≡ 232515905)
no₃ ()

TX≢ : ¬ (cv TX ≡ R.TX)
TX≢ e = no₁ (trans (sym hX-N) (trans (cong (hC 5) e) hX-C))

TU1≢ : ¬ (cv TU1 ≡ R.TU1)
TU1≢ e = no₂ (trans (sym hU-N) (trans (cong (hC 7) e) hU-C))

TU2≢ : ¬ (cv TU2 ≡ R.TU2)
TU2≢ e = no₃ (trans (sym h2-N) (trans (cong (hC 8) e) h2-C))
```

## §2 同一个输入 $f+f$: 分支被折与不被折

`φC`: CRw 的同底折叠 $\Omega_1\oplus 1\to\Omega_1$ 作用在 `up h` 上 (Fab6 的 `φ` 的对应物). 下面两条 `refl` 是 CRw 里的结构: 前缀进分支, 逐分支折叠. Fab6 这边 `f+f` 折出来是原子.

```agda
φC : C.HB XS → C.HB XS
φC h = F.Φ bX (C.hs C.hz) (wf bX (C.hs C.hz)) tt bX C.hz (sm (C.hsuc C.hself)) F.topL (C.up h) tt

Ω₁ᶜ : C.K XS
Ω₁ᶜ = C.hz , inj₂ tt

ι′ : C.Cd → C.HB XS
ι′ d = C.ι {C.Cd} {λ c → F.Tw C.S⊥ (C.hs c)} C.hz (C.up d)

Pd : C.Cd → C.HB XS
Pd d = φC (F.topL C.⊞ (C.hz C.⊞ ι′ d))

fab-atom : φ (topL N.⊞ topL) ≡ N.hE tt (φ topL) g₀
fab-atom = refl

crw-br : φC (F.topL C.⊞ F.topL) ≡ C.hΩ Ω₁ᶜ (λ c → φC (F.topL C.⊞ gt c))
crw-br = refl

crw-br₂ : φC (F.topL C.⊞ gt (C.hs C.hz)) ≡ C.hΩ Ω₁ᶜ Pd
crw-br₂ = refl
```

## §3 CRw 的 $f+f$ 里的 $\Omega_1$-种类结点

`cnt c h`: 沿 $h$ 走: 遇到 $\Omega_1$ 种类的结点计 1 并进坐标 $c$ 处的分支; 遇到别的种类进最低坐标; ℕ-极限逐项. 这是 `NegFab6Sim.er` 的对应物 (Fab6 里 $\Omega_1$ 种类对应外部结点). 序 `_≼c_` 同 `NegFab6Sim._≼_` 在 `Cd` 上.

```agda
infix 4 _≼c_
data _≼c_ : C.Cd → C.Cd → Set where
  z≼ : ∀ {y} → C.hz ≼c y
  s≼s : ∀ {x y} → x ≼c y → C.hs x ≼c C.hs y
  l≼ : ∀ {f y} → (∀ n → f n ≼c y) → C.hl f ≼c y
  ≼l : ∀ {x f} n → x ≼c f n → x ≼c C.hl f
  ≼s : ∀ {x y} → x ≼c y → x ≼c C.hs y

rf : ∀ x → x ≼c x
rf C.hz = z≼
rf (C.hs x) = s≼s (rf x)
rf (C.hl f) = l≼ (λ n → ≼l n (rf (f n)))
rf (C.hΩ () _)

tr : ∀ {a b c} → a ≼c b → b ≼c c → a ≼c c
tr z≼ q = z≼
tr (l≼ k) q = l≼ (λ n → tr (k n) q)
tr p (≼l n q) = ≼l n (tr p q)
tr p (≼s q) = ≼s (tr p q)
tr (s≼s p) (s≼s q) = s≼s (tr p q)
tr (≼s p) (s≼s q) = ≼s (tr p q)
tr (≼l n p) (l≼ k) = tr p (k n)

⊞l : ∀ x y → x ≼c x C.⊞ y
⊞l x C.hz = rf x
⊞l x (C.hs y) = ≼s (⊞l x y)
⊞l x (C.hl f) = ≼l 0 (⊞l x (f 0))
⊞l x (C.hΩ () _)

⊞r : ∀ x y → y ≼c x C.⊞ y
⊞r x C.hz = z≼
⊞r x (C.hs y) = s≼s (⊞r x y)
⊞r x (C.hl f) = l≼ (λ n → ≼l n (⊞r x (f n)))
⊞r x (C.hΩ () _)

⊞m : ∀ {x x′ y y′} → x ≼c x′ → y ≼c y′ → x C.⊞ y ≼c x′ C.⊞ y′
⊞m {x′ = x′} {y′ = y′} p z≼ = tr p (⊞l x′ y′)
⊞m p (s≼s q) = s≼s (⊞m p q)
⊞m p (l≼ k) = l≼ (λ n → ⊞m p (k n))
⊞m p (≼l n q) = ≼l n (⊞m p q)
⊞m p (≼s q) = ≼s (⊞m p q)

cnt : C.Cd → C.HB XS → C.Cd
cnt c C.hz = C.hz
cnt c (C.hs h) = C.hs (cnt c h)
cnt c (C.hl f) = C.hl (λ n → cnt c (f n))
cnt c (C.hΩ (C.hz , inj₂ _) g) = C.hs (cnt c (g c))
cnt c (C.hΩ (C.hz , inj₁ ()) g)
cnt c (C.hΩ (C.hs x , κ) g) = cnt c (g (C.bot XS (C.hs x , κ)))
cnt c (C.hΩ (C.hl f , κ) g) = cnt c (g (C.bot XS (C.hl f , κ)))
cnt c (C.hΩ (C.hΩ () _ , _) g)

cnt-⊞ : ∀ c a b → cnt c a C.⊞ cnt c b ≼c cnt c (a C.⊞ b)
cnt-⊞ c a C.hz = rf (cnt c a)
cnt-⊞ c a (C.hs b) = s≼s (cnt-⊞ c a b)
cnt-⊞ c a (C.hl f) = l≼ (λ n → ≼l n (cnt-⊞ c a (f n)))
cnt-⊞ c a (C.hΩ (C.hz , inj₂ _) g) = s≼s (cnt-⊞ c a (g c))
cnt-⊞ c a (C.hΩ (C.hz , inj₁ ()) g)
cnt-⊞ c a (C.hΩ (C.hs x , κ) g) = cnt-⊞ c a (g (C.bot XS (C.hs x , κ)))
cnt-⊞ c a (C.hΩ (C.hl f , κ) g) = cnt-⊞ c a (g (C.bot XS (C.hl f , κ)))
cnt-⊞ c a (C.hΩ (C.hΩ () _ , _) g)

pos : ∀ c d → C.hs C.hz ≼c cnt c (Pd d)
pos c C.hz = s≼s z≼
pos c (C.hs d) = ≼l 0 (pos c d)
pos c (C.hl f) = ≼l 0 (pos c (f 0))
pos c (C.hΩ () _)
```

**定理 (`crw-many`).** 对一切可数树 $c,d$: CRw 的 $\varphi(f+f)$ 的分支 $(1,d)$ (`crw-br`, `crw-br₂`) 里, 沿坐标 $c$ 数到的 $\Omega_1$ 种类结点不少于 $d$. 没有与 $d$ 无关的可数上界; Fab6 里同一个输入的外部结点个数是 $2$ 加前缀的 $1$ (`NegFab6.atoms-f₂`, `er` 的值 $3$).

```agda
crw-many : ∀ c d → d ≼c cnt c (Pd d)
crw-Σ : ∀ c (f : ℕ → C.Cd) n → f n ≼c cnt c (Σ⁺ (λ m → Pd (f m)) n)
crw-many c C.hz = z≼
crw-many c (C.hs d) = ≼l 1 (tr (⊞m (crw-many c d) (pos c d)) (cnt-⊞ c (Pd d) (Pd d)))
crw-many c (C.hl f) = l≼ (λ n → ≼l n (crw-Σ c f n))
crw-many c (C.hΩ () _)
crw-Σ c f zero = crw-many c (f 0)
crw-Σ c f (suc n) = tr (tr (crw-many c (f (suc n))) (⊞r (cnt c (Σ⁺ (λ m → Pd (f m)) n)) (cnt c (Pd (f (suc n))))))
                       (cnt-⊞ c (Σ⁺ (λ m → Pd (f m)) n) (Pd (f (suc n))))
```
