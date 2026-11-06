# 层号一次封闭: 与 `HtFeed` 的高度互通, 闭项

> 不含记号. 入口 [LFRe](LFRe.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.
>
> 这一篇做三件事, 都是定理:
>
> 1. 第 0 层的值 `HB (Lv lz)` 与 `A` 互通 (`ofA`, `toA`), 保第一位置与合法.
> 2. `HtFeedTree.H` 的合法高度是 `SL` 的合法高度 (`ofH`, `Lg-ofH`). 所以折叠输出经和读回的高度, 例如 `HtOutFeed` 的回灌高度 `Λs n`, `Λω`, 在一次封闭的类型里**字面合法** (`Lg-chain`, `Lg-chainω`), 合法性来自 `Lg-rd` 与 `Lg-sum`, 不来自 `HS`.
> 3. 反过来, `SL` 里只用第 0 层新种类的高度 (`Fr`) 读成 `H` 保合法 (`toH`, `Lg-toH`), 于是这样的层号有 $\psi_0(\Omega_x)$ 的闭项 (`ψ₀ᴸ`), 类型是 `A` (布劳威尔树), 有 FGH. 折叠是 `HtFeedClosed.TΛ`, 一行没改.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LFReBr where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]; [_,_]′)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; ⊲-tr; lg⊲; z⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtTowerTy
open import OCF.Align.LFReTy
open import OCF.Align.LFReTower
import OCF.Align.HtFeedTree as F
```

## §1 第 0 层的值与 `A`

`toA ∘ ofA` 不是字面的恒等 (极限处要函数外延), 所以不用它. 要的是 `lift`: `toA b` 的一切第一位置都字面地是 `toA` 在 $b$ 的某个第一位置上的值; `liftO` 对 `ofA` 同样.

```agda
B₀ : Set
B₀ = HB (Lv lz)

ofA : A → B₀
ofA azero = hz
ofA (asuc a) = hs (ofA a)
ofA (alim f) = hl (λ n → ofA (f n))

toA : B₀ → A
toA hz = azero
toA (hs c) = asuc (toA c)
toA (hl f) = alim (λ n → toA (f n))
toA (hΩ () g)

ofA-⊲ : ∀ {a b w} → a ⊲ b → ofA a ⊲[ w ] ofA b
ofA-⊲ C.self = hself
ofA-⊲ (C.suc p) = hsuc (ofA-⊲ p)
ofA-⊲ (C.lim n p) = hlim n (ofA-⊲ p)

toA-⊲ : ∀ {a b w} → a ⊲[ w ] b → toA a ⊲ toA b
toA-⊲ hself = C.self
toA-⊲ (hsuc p) = C.suc (toA-⊲ p)
toA-⊲ (hlim n p) = C.lim n (toA-⊲ p)
toA-⊲ (hLim {κ = ()} e p)

Lg-ofA : ∀ a → Lg a → LgB (ofA a)
Lg-ofA azero l = tt
Lg-ofA (asuc a) l = Lg-ofA a l
Lg-ofA (alim f) (st , l) = (λ n → ofA-⊲ (st n)) , (λ n → Lg-ofA (f n) (l n))

Lg-toA : ∀ c → LgB c → Lg (toA c)
Lg-toA hz l = tt
Lg-toA (hs c) l = Lg-toA c l
Lg-toA (hl f) (st , l) = (λ n → toA-⊲ (st {tt} n)) , (λ n → Lg-toA (f n) (l n))
Lg-toA (hΩ () g) l

lift : ∀ {c} b {w} → c ⊲ toA b → Σ B₀ (λ x → (x ⊲[ w ] b) × (toA x ≡ c))
lift hz C.self = hz , hself , refl
lift (hs b) C.self = hs b , hself , refl
lift (hl f) C.self = hl f , hself , refl
lift (hs b) (C.suc p) with lift b p
... | x , q , eq = x , hsuc q , eq
lift (hl f) (C.lim n p) with lift (f n) p
... | x , q , eq = x , hlim n q , eq
lift (hΩ () g) p

liftO : ∀ {x} V {w} → x ⊲[ w ] ofA V → Σ A (λ a → (a ⊲ V) × (ofA a ≡ x))
liftO azero hself = azero , C.self , refl
liftO (asuc V) hself = asuc V , C.self , refl
liftO (alim f) hself = alim f , C.self , refl
liftO (asuc V) (hsuc q) with liftO V q
... | a , p , eq = a , C.suc p , eq
liftO (alim f) (hlim n q) with liftO (f n) q
... | a , p , eq = a , C.lim n p , eq
```

## §2 `H` 放进 `SL`

$\Omega$-分支放在第 0 层的新种类 `νL lz` 上. 世界的对应: `H` 的世界取 `SL` 的世界在第 0 层的界读成 `A`.

```agda
ofH : F.H → HB SL
ofH F.hz = hz
ofH (F.hs x) = hs (ofH x)
ofH (F.hl f) = hl (λ n → ofH (f n))
ofH (F.hΩ g) = hΩ (νL lz) (λ c → ofH (g (toA c)))

bnd₀ : Wd SL → B₀
bnd₀ W = proj₂ (W lz)

ofH-⊲ : ∀ {a b W} → a F.⊲[ toA (bnd₀ W) ] b → ofH a ⊲[ W ] ofH b
ofH-⊲ F.hself = hself
ofH-⊲ (F.hsuc p) = hsuc (ofH-⊲ p)
ofH-⊲ (F.hlim n p) = hlim n (ofH-⊲ p)
ofH-⊲ {a} {W = W} (F.hLim {g = g} e p) with lift (bnd₀ W) {proj₁ (W lz)} e
... | x , q , eq = hLim {c = x} q (subst (λ z → ofH a ⊲[ W ] ofH (g z)) (sym eq) (ofH-⊲ p))

Lg-ofH : ∀ h → F.LgH h → LgB (ofH h)
Lg-ofH F.hz l = tt
Lg-ofH (F.hs h) l = Lg-ofH h l
Lg-ofH (F.hl f) (st , l) = (λ {W} n → ofH-⊲ {W = W} (F.⊲ᴴ0 (st n))) , (λ n → Lg-ofH (f n) (l n))
Lg-ofH (F.hΩ g) (mo , l) =
  (λ {W} {c} {c′} lw e e′ p →
     ofH-⊲ {W = W} (F.⊲ᴴ↑ (toA-⊲ e′) (mo (Lg-toA c′ (lgB⊲ e′ tt (proj₂ (lw lz)))) (toA-⊲ p)))) ,
  (λ c lc → Lg-ofH (g (toA c)) (l (toA c) (Lg-toA c lc)))
```

**链点字面合法.** `HtOutFeed` 的回灌高度是第 1 层的折叠输出经 `rd` 读出, 它们的合法性是 `Lg-rd` (形状). 放进 `SL` 仍合法. 第 0 层的链点是 `sum` 的值, 合法性是 `Lg-sum`; 放进第 0 层的值仍合法. 旧证书缺的就是这一条 (`NoKCertNeg.no-HS→Lgl`: `HS` 给不出字面 `Lgl`); 这里它由和的形状给出, 不经 `HS`.

```agda
import OCF.Align.HtOutFeed as O

chain : ℕ → HB SL
chain n = ofH (proj₁ (O.Λs n))

Lg-chain : ∀ n → LgB (chain n)
Lg-chain n = Lg-ofH (proj₁ (O.Λs n)) (proj₂ (O.Λs n))

chainω : HB SL
chainω = ofH O.Λω

Lg-chainω : LgB chainω
Lg-chainω = Lg-ofH O.Λω O.lΛω

Lg-chain₀ : ∀ {W} b (d : F.D₀ W) → Lg b → LgB (ofA (F.sum b d))
Lg-chain₀ b d l = Lg-ofA (F.sum b d) (F.Lg-sum b d l)

fst-chain₀ : ∀ {W w} b (d : F.D₀ W) → ofA b ⊲[ w ] ofA (F.sum b d)
fst-chain₀ b d = ofA-⊲ (F.sum-fst b d)
```

## §3 `SL` 的第 0 层片段读回 `H`

`Fr h`: $h$ 的 $\Omega$-节点都在 `νL lz` 上. `toH` 是全函数 (别的种类给 `hz`, 不会用到), `Fr` 只作前提, 所以结果不依赖 `Fr` 的证据.

```agda
Fr : HB SL → Set
Fr hz = ⊤
Fr (hs h) = Fr h
Fr (hl f) = ∀ n → Fr (f n)
Fr (hΩ (lz , inj₂ _) g) = ∀ c → Fr (g c)
Fr (hΩ (lz , inj₁ ()) g)
Fr (hΩ (ls _ , _) g) = ⊥
Fr (hΩ (ll _ , _) g) = ⊥
Fr (hΩ (lΩ _ _ , _) g) = ⊥

toH : HB SL → F.H
toH hz = F.hz
toH (hs h) = F.hs (toH h)
toH (hl f) = F.hl (λ n → toH (f n))
toH (hΩ (lz , inj₂ _) g) = F.hΩ (λ a → toH (g (ofA a)))
toH (hΩ (lz , inj₁ ()) g)
toH (hΩ (ls _ , _) g) = F.hz
toH (hΩ (ll _ , _) g) = F.hz
toH (hΩ (lΩ _ _ , _) g) = F.hz
```

读回要一个 `SL` 的世界, 它在第 0 层的界是给定的 $V$, 别的层取最小的界. `w₀ k` 是 `Lv k` 的最小世界, 对 $k$ 递归.

```agda
w₀ : (k : LH) → Wd (Lv k)
w₀ lz = tt
w₀ (ls x) = w₀ x , hz
w₀ (ll f) = λ n → w₀ (f n)
w₀ (lΩ k g) = [_,_] {C = λ i → Wd ([ (λ _ → step (Lv k)) , (λ c → Lv (g c)) ]′ i)} (λ _ → w₀ k , hz) (λ c → w₀ (g c))

Lg-w₀ : ∀ k → LgW (Lv k) (w₀ k)
Lg-w₀ lz = tt
Lg-w₀ (ls x) = Lg-w₀ x , tt
Lg-w₀ (ll f) = λ n → Lg-w₀ (f n)
Lg-w₀ (lΩ k g) = [_,_] {C = λ i → LgW ([ (λ _ → step (Lv k)) , (λ c → Lv (g c)) ]′ i) (w₀ (lΩ k g) i)} (λ _ → Lg-w₀ k , tt) (λ c → Lg-w₀ (g c))

bndV : A → (k : LH) → HB (Lv k)
bndV V lz = ofA V
bndV V (ls _) = hz
bndV V (ll _) = hz
bndV V (lΩ _ _) = hz

Wc : A → Wd SL
Wc V k = w₀ k , bndV V k

Lg-Wc : ∀ V → Lg V → LgW SL (Wc V)
Lg-Wc V lV lz = tt , Lg-ofA V lV
Lg-Wc V lV (ls k) = Lg-w₀ (ls k) , tt
Lg-Wc V lV (ll f) = Lg-w₀ (ll f) , tt
Lg-Wc V lV (lΩ k g) = Lg-w₀ (lΩ k g) , tt

Fr-⊲ : ∀ {a b W} → a ⊲[ W ] b → Fr b → Fr a
Fr-⊲ hself f = f
Fr-⊲ (hsuc p) f = Fr-⊲ p f
Fr-⊲ (hlim n p) f = Fr-⊲ p (f n)
Fr-⊲ (hLim {κ = lz , inj₂ _} {c = c} e p) f = Fr-⊲ p (f c)
Fr-⊲ (hLim {κ = lz , inj₁ ()} e p) f
Fr-⊲ (hLim {κ = ls _ , _} e p) ()
Fr-⊲ (hLim {κ = ll _ , _} e p) ()
Fr-⊲ (hLim {κ = lΩ _ _ , _} e p) ()

toH-⊲ : ∀ {V a b} → a ⊲[ Wc V ] b → Fr b → toH a F.⊲[ V ] toH b
toH-⊲ hself f = F.hself
toH-⊲ (hsuc p) f = F.hsuc (toH-⊲ p f)
toH-⊲ (hlim n p) f = F.hlim n (toH-⊲ p (f n))
toH-⊲ {V} {a} (hLim {κ = lz , inj₂ _} {g = g} {c = x} e p) f with liftO V e
... | b , q , eq = F.hLim q (subst (λ z → toH a F.⊲[ V ] toH (g z)) (sym eq) (toH-⊲ p (f x)))
toH-⊲ (hLim {κ = lz , inj₁ ()} e p) f
toH-⊲ (hLim {κ = ls _ , _} e p) ()
toH-⊲ (hLim {κ = ll _ , _} e p) ()
toH-⊲ (hLim {κ = lΩ _ _ , _} e p) ()

Lg-toH : ∀ h → Fr h → LgB h → F.LgH (toH h)
Lg-toH hz fr l = tt
Lg-toH (hs h) fr l = Lg-toH h fr l
Lg-toH (hl f) fr (st , l) =
  (λ n → toH-⊲ {azero} (st {Wc azero} n) (fr (suc n))) , (λ n → Lg-toH (f n) (fr n) (l n))
Lg-toH (hΩ (lz , inj₂ _) g) fr (mo , l) =
  (λ {c} {c′} lc′ p →
     toH-⊲ {c′} (mo {Wc c′} (Lg-Wc c′ lc′) (ofA-⊲ p) hself (ofA-⊲ p)) (fr (ofA c′))) ,
  (λ c lc → Lg-toH (g (ofA c)) (fr (ofA c)) (l (ofA c) (Lg-ofA c lc)))
Lg-toH (hΩ (lz , inj₁ ()) g) fr l
Lg-toH (hΩ (ls _ , _) g) () l
Lg-toH (hΩ (ll _ , _) g) () l
Lg-toH (hΩ (lΩ _ _ , _) g) () l
```

## §4 闭项

`ψ₀ᴸ h`: 层号 $h$ (在片段里, 合法) 的 $\psi_0(\Omega_h)$, 一个 `A`. 读法 (判断, 按 `HtFeed` 的读法): `ψ₀Ω₁` 读 $\psi_0(\Omega_\Omega)$, `ψ₀Ω₁+1` 读 $\psi_0(\Omega_{\Omega+1})$, `ψ₀Ω₁·2` 读 $\psi_0(\Omega_{\Omega\cdot2})$, `ψ₀-chainω` 读 `HtOutFeed.T-fbω` 的那一个. 它们都过了旧证书的第一个障碍 $\psi_0(\Omega_\Omega)$: 层号在一次封闭的类型里, 合法性由形状给出, 闭项是布劳威尔树, 有 FGH.

```agda
open import OCF.Align.HtFeedClosed using (TΛ; Lg-TΛ; ord)
import OCF.Free.Level as FLv

ψ₀ᴸ : (h : HB SL) → Fr h → LgB h → A
ψ₀ᴸ h fr l = TΛ (toH h) (Lg-toH h fr l)

Lg-ψ₀ᴸ : ∀ h fr l → Lg (ψ₀ᴸ h fr l)
Lg-ψ₀ᴸ h fr l = Lg-TΛ (toH h) (Lg-toH h fr l)

Fr-⊞ : ∀ a b → Fr a → Fr b → Fr (a ⊞ b)
Fr-⊞ a hz fa fb = fa
Fr-⊞ a (hs b) fa fb = Fr-⊞ a b fa fb
Fr-⊞ a (hl f) fa fb = λ n → Fr-⊞ a (f n) fa (fb n)
Fr-⊞ a (hΩ (lz , inj₂ _) g) fa fb = λ c → Fr-⊞ a (g c) fa (fb c)
Fr-⊞ a (hΩ (lz , inj₁ ()) g) fa fb
Fr-⊞ a (hΩ (ls _ , _) g) fa ()
Fr-⊞ a (hΩ (ll _ , _) g) fa ()
Fr-⊞ a (hΩ (lΩ _ _ , _) g) fa ()

Fr-ι₀ : ∀ c → Fr (ιL lz (up c))
Fr-ι₀ hz = tt
Fr-ι₀ (hs c) = Fr-ι₀ c
Fr-ι₀ (hl f) = λ n → Fr-ι₀ (f n)
Fr-ι₀ (hΩ () g)

Fr-Ω₁ : Fr Ω₁
Fr-Ω₁ = λ c → Fr-⊞ (hs hz) (ιL lz (up c)) tt (Fr-ι₀ c)

Fr-ofH : ∀ x → Fr (ofH x)
Fr-ofH F.hz = tt
Fr-ofH (F.hs x) = Fr-ofH x
Fr-ofH (F.hl f) = λ n → Fr-ofH (f n)
Fr-ofH (F.hΩ g) = λ c → Fr-ofH (g (toA c))

ψ₀Ω₁ ψ₀Ω₁+1 ψ₀Ω₁·2 : A
ψ₀Ω₁ = ψ₀ᴸ Ω₁ Fr-Ω₁ (Lg-tw 2)
ψ₀Ω₁+1 = ψ₀ᴸ (hs Ω₁) Fr-Ω₁ (Lg-tw 2)
ψ₀Ω₁·2 = ψ₀ᴸ (Ω₁ ⊞ Ω₁) (Fr-⊞ Ω₁ Ω₁ Fr-Ω₁ Fr-Ω₁) (Lg-⊞ Ω₁ Ω₁ (Lg-tw 2) (Lg-tw 2))

ψ₀-chainω : A
ψ₀-chainω = ψ₀ᴸ chainω (Fr-ofH O.Λω) Lg-chainω

fgh : ℕ → ℕ
fgh = FLv.FGH (ord ψ₀Ω₁·2)
```

**片段的边.** `tw 3` ($\Omega_\Omega$) 与 $\Lambda$ 不在片段里: `tw 3` 在坐标 $1$ 处的分支是 `Ω̂ (hs (hs hz))`, 种类 `νL (ls lz)` ($\Omega_2$). 这就是第一个障碍的位置 (编译, 一行).

```agda
open import Relation.Nullary using (¬_)

no-Fr-tw3 : ¬ Fr (tw 3)
no-Fr-tw3 f = f (hs hz)

no-Fr-Λ : ¬ Fr Λ
no-Fr-Λ f = no-Fr-tw3 (f 3)
```
