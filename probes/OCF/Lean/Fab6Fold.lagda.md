# Fab6 (二): 塔与同底折叠 (对一切底与外部种类一份)

> 不含记号. 入口 [Fab6](Fab6.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.
>
> **重写** (参考 `CRwFold` 的同底部分, 只作参考). 塔 `Tw S m` 同 CRw. 折叠 `Φ` 只有同底子句: 底种类留, 塔的新种类用 `cmpB` 以层号 $m$ 为公共上界比较 (留 / 同层 / 在上); 外部结点 `hE` **原样留下** (分支在别的层上, 本层的折叠不进去), 只折前缀. CRw 的跨底子句 (`cx`), 路径 (`Nd`), 策略 (`Po`, `pX`), 都不在这里: 跨底折叠在入口文件里, 只有一个结点种类要处理.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.Fab6Fold where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import OCF.Lean.Fab6Base
```

## §1 塔

第 $m$ 层 ($m$ 可数层号) 的种类结构: 底 `S` 上, 后继给 `step`, ℕ-极限给 `sup ℕ`. 外部种类 `X` 不进塔的结构, 只进树.

```agda
Tw : XK → KS → Cd → KS
Tw X S hz = S
Tw X S (hs x) = step X (Tw X S x)
Tw X S (hl f) = sup ℕ (λ n → Tw X S (f n))
Tw X S (hΩ () _)
Tw X S (hE () _ _)
```

## §2 种类: 分类, 嵌入, `along`

```agda
module _ {X : XK} {S : KS} where
  data Cl (m : Cd) (κ : K (Tw X S m)) : Set where
    bas : (κ₀ : K S) → (E S κ₀ → E (Tw X S m) κ) → Cl m κ
    nw  : (j : Cd) → hs j ⊲ m → (HB X (Tw X S j) → E (Tw X S m) κ) → Cl m κ

  cS : ∀ {x κ} → Cl x κ → Cl (hs x) (inj₁ κ)
  cS (bas κ₀ to) = bas κ₀ to
  cS (nw j p to) = nw j (hsuc p) to

  cL : ∀ {f} n {κ} → Cl (f n) κ → Cl (hl f) (n , κ)
  cL n (bas κ₀ to) = bas κ₀ to
  cL n (nw j p to) = nw j (hlim n p) to

  cl : ∀ m κ → Cl m κ
  cl hz κ = bas κ (λ e → e)
  cl (hs x) (inj₁ κ) = cS (cl x κ)
  cl (hs x) (inj₂ _) = nw x hself (λ c → c)
  cl (hl f) (n , κ) = cL n (cl (f n) κ)
  cl (hΩ () _) _
  cl (hE () _ _) _

  emb : ∀ t → K S → K (Tw X S t)
  emb hz κ = κ
  emb (hs x) κ = inj₁ (emb x κ)
  emb (hl f) κ = 0 , emb (f 0) κ
  emb (hΩ () _) _
  emb (hE () _ _) _

  frE : ∀ t κ → E (Tw X S t) (emb t κ) → E S κ
  frE hz κ c = c
  frE (hs x) κ c = frE x κ c
  frE (hl f) κ c = frE (f 0) κ c
  frE (hΩ () _) _ _
  frE (hE () _ _) _ _

  along : ∀ {i t} → hs i ⊲ t → K (Tw X S t)
  along hself = inj₂ tt
  along (hsuc q) = inj₁ (along q)
  along (hlim n q) = n , along q
  along (hLim {κ = ()} _ _)
  along (hEx {x = ()} _)

  frA : ∀ {i t} (q : hs i ⊲ t) → E (Tw X S t) (along q) → HB X (Tw X S i)
  frA hself c = c
  frA (hsuc q) c = frA q c
  frA (hlim n q) c = frA q c
  frA (hLim {κ = ()} _ _) _
  frA (hEx {x = ()} _) _
```

## §3 决定

同 CRw: `Dc L X t A`: 留 (`keep`), 同层 (`same`), 在上 (`above`); `pick` 由 `cmpB` 的结果读出.

```agda
data Dc (L : Cd → KS) (X : XK) (B t : Cd) (A : Set) : Set where
  keep  : (κ′ : K (L t)) → (E (L t) κ′ → A) → Dc L X B t A
  same  : (HB X (L t) → A) → Dc L X B t A
  above : (i : Cd) → hs i ⊲ B → t ⊲ i → (HB X (L i) → A) → Dc L X B t A

caseDc : ∀ {L X B t A} {R : Set} → Dc L X B t A →
         ((κ′ : K (L t)) → (E (L t) κ′ → A) → R) → ((HB X (L t) → A) → R) →
         ((i : Cd) → hs i ⊲ B → t ⊲ i → (HB X (L i) → A) → R) → R
caseDc (keep κ′ fr) k s ab = k κ′ fr
caseDc (same to) k s ab = s to
caseDc (above i u q to) k s ab = ab i u q to

pick : ∀ X S {B t i A} → (HB X (Tw X S i) → A) → hs i ⊲ B → (t ⊲ hs i) ⊎ (hs i ⊲ t) → Dc (Tw X S) X B t A
pick X S to u (inj₂ q) = keep (along q) (λ c → to (frA q c))
pick X S to u (inj₁ hself) = keep (inj₂ tt) to
pick X S to u (inj₁ (hsuc hself)) = same to
pick X S to u (inj₁ (hsuc q)) = above _ u q to

dcl : ∀ {X S m t κ} → t ⊲ m → LgB m → Cl {X} {S} m κ → Dc (Tw X S) X m t (E (Tw X S m) κ)
dcl {t = t} pt lm (bas κ₀ to) = keep (emb t κ₀) (λ c → to (frE t κ₀ c))
dcl {X} {S} pt lm (nw j pj to) = pick X S to pj (cmpB pj pt tt lm)
```

## §4 地板, 可达性, 累加

```agda
topT : ∀ X S → HB X S → ∀ m → HB X (Tw X S m)
ΣT : ∀ X S → HB X S → (f : ℕ → Cd) → ℕ → HB X (Tw X S (hl f))
topT X S b hz = b
topT X S b (hs x) = hΩ (inj₂ tt) up
topT X S b (hl f) = hl (ΣT X S b f)
topT X S b (hΩ () _)
topT X S b (hE () _ _)
ΣT X S b f zero = ι 0 (topT X S b (f 0))
ΣT X S b f (suc n) = ΣT X S b f n ⊞ ι (suc n) (topT X S b (f (suc n)))

data Acc (m : Cd) : Set where
  acc : (∀ i → hs i ⊲ m → Acc i) → Acc m

wf : ∀ m → Acc m
g⊲ : ∀ m i → hs i ⊲ m → Acc i
wf m = acc (g⊲ m)
g⊲ (hs x) .x hself = wf x
g⊲ (hs x) i (hsuc p) = g⊲ x i p
g⊲ (hl f) i (hlim n p) = g⊲ (f n) i p
g⊲ (hΩ () _) i _
g⊲ (hE () _ _) i _

module _ {X : XK} {S : KS} where
  mul : HB X S → ℕ → HB X S
  mul x zero = x
  mul x (suc n) = mul x n ⊞ x

  chain : HB X S → (HB X S → HB X S) → ℕ → HB X S
  chain b k zero = k b
  chain b k (suc n) = chain b k n ⊞ k (b ⊞ chain b k n)

  Σ⁺ : (ℕ → HB X S) → ℕ → HB X S
  Σ⁺ f zero = f 0
  Σ⁺ f (suc n) = Σ⁺ f n ⊞ f (suc n)

lg↓ : ∀ {i B} → hs i ⊲ B → LgB B → LgB i
lg↓ p l = lgB⊲ (⊲ᴮ-tr (hsuc hself) p) tt l

⊏⊑ : ∀ {i B} → hs i ⊲ B → i ⊲ B
⊏⊑ p = ⊲ᴮ-tr (hsuc hself) p
```

## §5 同底折叠

`Φ m a lm t pt b h`: 把第 $m$ 层的高度 $h$ 折到第 $t$ 层 ($t\lhd m$), 当前界 $b$. 外部结点留下, 前缀照折.

```agda
module _ {X : XK} {S : KS} where
  Φ : ∀ m → Acc m → LgB m → ∀ t → t ⊲ m → HB X (Tw X S t) → HB X (Tw X S m) → HB X (Tw X S t)
  Φ m a lm t pt b hz = hs hz
  Φ m a lm t pt b (hs h) = hl (mul (Φ m a lm t pt b h))
  Φ m a lm t pt b (hl f) = hl (Σ⁺ (λ n → Φ m a lm t pt b (f n)))
  Φ m a lm t pt b (hE x p g) = hE x (Φ m a lm t pt b p) g
  Φ m (acc rs) lm t pt b (hΩ κ g) = caseDc (dcl pt lm (cl m κ))
    (λ κ′ fr → hΩ κ′ (λ c → Φ m (acc rs) lm t pt b (g (fr c))))
    (λ to → hl (chain b (λ b′ → Φ m (acc rs) lm t pt b′ (g (to b′)))))
    (λ i pi q to → Φ i (rs i pi) (lg↓ pi lm) t q b
       (hl (chain (topT X S (topT X S hz hz) i) (λ b′ → Φ m (acc rs) lm i (⊏⊑ pi) b′ (g (to b′))))))
```

(在上的链以第 $i$ 层的地板 `topT X S hz i` 起步, 同 CRw 的 `top s i` 在空底上; `topT X S hz hz = hz`, 写成 `topT X S (topT X S hz hz) i` 只是为了让 `S` 显式.)

## §6 形状给出的合法

```agda
module _ {X : XK} {S : KS} where
  Sh : HB X S → Set
  Sh hz = ⊤
  Sh (hs h) = Sh h
  Sh (hl f) = (∀ {w : Wd S} n → f n ⊲[ w ] f (suc n)) × (∀ n → Sh (f n))
  Sh (hΩ κ g) = ∀ c → Sh (g c)
  Sh (hE x p g) = Sh p

  Sh-⊞ : ∀ a b → Sh a → Sh b → Sh (a ⊞ b)
  Sh-⊞ a hz sa sb = sa
  Sh-⊞ a (hs b) sa sb = Sh-⊞ a b sa sb
  Sh-⊞ a (hl f) sa (st , sf) = (λ n → ⊞-⊲ a (st n)) , (λ n → Sh-⊞ a (f n) sa (sf n))
  Sh-⊞ a (hΩ κ g) sa sg = λ c → Sh-⊞ a (g c) sa (sg c)
  Sh-⊞ a (hE x p g) sa sp = Sh-⊞ a p sa sp

  Sh-mul : ∀ x → Sh x → Sh (hl (mul x))
  Sh-mul x s = (λ n → ⊞-fst (mul x n) x) , go
    where go : ∀ n → Sh (mul x n)
          go zero = s
          go (suc n) = Sh-⊞ _ x (go n) s

  Sh-chain : ∀ b k → (∀ b′ → Sh (k b′)) → Sh (hl (chain b k))
  Sh-chain b k sk = (λ n → ⊞-fst (chain b k n) (k (b ⊞ chain b k n))) , go
    where go : ∀ n → Sh (chain b k n)
          go zero = sk b
          go (suc n) = Sh-⊞ _ _ (go n) (sk _)

  Sh-Σ : ∀ f → (∀ n → Sh (f n)) → Sh (hl (Σ⁺ f))
  Sh-Σ f sf = (λ n → ⊞-fst (Σ⁺ f n) (f (suc n))) , go
    where go : ∀ n → Sh (Σ⁺ f n)
          go zero = sf 0
          go (suc n) = Sh-⊞ _ _ (go n) (sf (suc n))

Sh-case : ∀ {L X B t A} {S : KS} (d : Dc L X B t A) {k s ab} →
          (∀ κ′ fr → Sh {X} {S} (k κ′ fr)) → (∀ to → Sh {X} {S} (s to)) → (∀ i u q to → Sh {X} {S} (ab i u q to)) →
          Sh (caseDc d k s ab)
Sh-case (keep κ′ fr) sk ss sa = sk κ′ fr
Sh-case (same to) sk ss sa = ss to
Sh-case (above i u q to) sk ss sa = sa i u q to

module _ {X : XK} {S : KS} where
  Sh-Φ : ∀ m a lm t pt b h → Sh (Φ {X} {S} m a lm t pt b h)
  Sh-Φ m a lm t pt b hz = tt
  Sh-Φ m a lm t pt b (hs h) = Sh-mul _ (Sh-Φ m a lm t pt b h)
  Sh-Φ m a lm t pt b (hl f) = Sh-Σ _ (λ n → Sh-Φ m a lm t pt b (f n))
  Sh-Φ m a lm t pt b (hE x p g) = Sh-Φ m a lm t pt b p
  Sh-Φ m (acc rs) lm t pt b (hΩ κ g) = Sh-case (dcl pt lm (cl m κ))
    (λ κ′ fr c → Sh-Φ m (acc rs) lm t pt b (g (fr c)))
    (λ to → Sh-chain b _ (λ b′ → Sh-Φ m (acc rs) lm t pt b′ (g (to b′))))
    (λ i pi q to → Sh-Φ i (rs i pi) (lg↓ pi lm) t q b _)

-- 第 0 层没有种类: 形状就是合法
sh→lg : ∀ (h : Cd) → Sh h → LgB h
sh→lg hz s = tt
sh→lg (hs h) s = sh→lg h s
sh→lg (hl f) (st , s) = (λ {w} n → st {w} n) , (λ n → sh→lg (f n) (s n))
sh→lg (hΩ () _) s
sh→lg (hE () _ _) s
```
