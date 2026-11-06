# 事件世界上的真折叠 (二): 读回与丢掉事件

> 不含记号. 入口 [EvFold](EvFold.lagda.md). 两个事件种类各有一个读回层:
>
> - κ₀ (坐标 $H_0$): 第 1 层的树读成 $H_0$ 的高度 (`rd₁`, 与 `HtTowerFRead.rd` 同形; 第 1 层没有事件闭包, `ze1`).
> - κ₁ (坐标 `HB S₁`): 第 2 层的树读成 `HB S₁` 的高度 (`rd₂`, 与 `HtTowerNRead.rd₂` 同形). 过第 1 层的节点读成新种类 `σH` 的分支 (坐标 $x$ 喂 `toD₁ x`); **κ₀ 的闭包 `nε κ₀` 也读成 `σH` 的分支**, 坐标 $x$ 上的世界是**加一个 κ₀ 事件**, 增量 $\mathrm{rd}_1(0,\mathrm{toD}_1\,x)$ (经第 1 层读回, 所以对任意 $x$ 都合法). 这一行就是 `HtTowerNRead` 里 "高度界升到 $\mathrm{rd}(w_1,\mathrm{toD}_1 x)$" 在事件世界上的形状.
> - `RB κ`: 读回层 `RLay κ` 的树读成种类 κ 的合法增量 (从 0 读起). 回灌时这个增量作为事件接到世界上 (`AdmEvBase.new-gen₀`: 界字面地接上它).
>
> **丢掉事件** (`drp₁`, `drp₂`): 读回层及以下的树换一个事件表. 分支所在的更大世界 $W''$ 的新事件**移植**到另一张表上 (`tp`: 后缀见证给出新事件, 接到别的底上). `drp₁`: 第 1 层没有事件闭包. `drp₂`: 第 2 层有 `nε κ₀`, 移植保留它的新事件. 读法上的依据 (判断, 部分是定理): κ₁ 的事件不进 κ₀ 的界 ([EvFoldNeg](EvFoldNeg.lagda.md) 的 `rp-κ₀-skip`), 所以第 2 层的树丢掉 κ₁ 的事件时, 它关心的 κ₀ 的界不变.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.EvFoldRead where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.List using (List; []; _∷_)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; ⊲-tr; lg⊲; z⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerCont using (nbᴮ; nb-contB; cont→Lg)
open import OCF.Align.HtTowerFRead using (nbA; Lg-nbA)
open import OCF.Align.HtTowerNRead using (nbAᵗ; Lg-nbAᵗ)
open import OCF.Align.EvFoldTree
```

## §1 坐标读成树

```agda
toD : ∀ {W} → A → D₀ W
toD azero = n0
toD (asuc c) = toD c ⨾ n1
toD (alim f) = nl (λ n → toD (f n))

D₁ D₂ : Wε → Set
D₁ = D (hs hz)
D₂ = D (hs (hs hz))

toD₁ : ∀ {W} → H₀ → D₁ W
toD₁ hz = n0
toD₁ (hs x) = toD₁ x ⨾ n1
toD₁ (hl f) = nl (λ n → toD₁ (f n))
toD₁ (hΩ tt h) = nκ tt (λ {c} _ _ → toD₁ (h c))

wκ : A → A → A
wκ w₀ c = sum {azero , []} w₀ (toD c)

lwκ : ∀ {w₀} c → Lg w₀ → Lg (wκ w₀ c)
lwκ {w₀} c l = Lg-sum w₀ (toD c) l

pwκ : ∀ w₀ c → w₀ ⊲ wκ w₀ c
pwκ w₀ c = sum-fst w₀ (toD c)
```

## §2 第 1 层读成 $H_0$

```agda
rd₁  : ∀ {W} → LgWε W → H₀ → D₁ W → H₀
rdp₁ : ∀ {W} → LgWε W → H₀ → (ℕ → D₁ W) → ℕ → H₀
rd₁ lW b n0 = b
rd₁ lW b n1 = hs b
rd₁ lW b (x ⨾ y) = rd₁ lW (rd₁ lW b x) y
rd₁ lW b (nl d) = hl (rdp₁ lW b d)
rd₁ lW b (ni (ss hself) u) = hΩ tt (nbA b (λ c h → rd₁ lW h (u ≤rf lW (toD c))))
rd₁ {W} lW b (nκ _ u) =
  hΩ tt (nbA b (λ c h → rd₁ (lwκ c (proj₁ lW) , tt) h (u (pwκ (proj₁ W) c) (lwκ c (proj₁ lW)))))
rd₁ lW b (nε κ zz u) = ⊥-elim (ze1 κ zz)
rd₁ lW b (nw p x) = rd₁ (lgW≤ p lW) b x
rdp₁ lW b d zero = b
rdp₁ lW b d (suc n) = rd₁ lW (rdp₁ lW b d n) (d n)

rd₁-fst : ∀ {W} (lW : LgWε W) b (x : D₁ W) {w} → b ⊲[ w ] rd₁ lW b x
rd₁-fst lW b n0 = hself
rd₁-fst lW b n1 = hsuc hself
rd₁-fst lW b (x ⨾ y) = ⊲ᴮ-tr (rd₁-fst lW b x) (rd₁-fst lW (rd₁ lW b x) y)
rd₁-fst lW b (nl d) = hlim 0 hself
rd₁-fst lW b (ni (ss hself) u) {w} = hLim {S₀} {c = azero} (z⊲ w) hself
rd₁-fst lW b (nκ _ u) {w} = hLim {S₀} {c = azero} (z⊲ w) hself
rd₁-fst lW b (nε κ zz u) = ⊥-elim (ze1 κ zz)
rd₁-fst lW b (nw p x) = rd₁-fst (lgW≤ p lW) b x

Lg-rd₁  : ∀ {W} (lW : LgWε W) b (x : D₁ W) → LgB b → LgB (rd₁ lW b x)
Lg-rdp₁ : ∀ {W} (lW : LgWε W) b (d : ℕ → D₁ W) → LgB b → ∀ n → LgB (rdp₁ lW b d n)
Lg-rd₁ lW b n0 l = l
Lg-rd₁ lW b n1 l = l
Lg-rd₁ lW b (x ⨾ y) l = Lg-rd₁ lW (rd₁ lW b x) y (Lg-rd₁ lW b x l)
Lg-rd₁ lW b (nl d) l = (λ n → rd₁-fst lW (rdp₁ lW b d n) (d n)) , Lg-rdp₁ lW b d l
Lg-rd₁ lW b (ni (ss hself) u) l =
  Lg-nbA (λ c h → rd₁-fst lW h (u ≤rf lW (toD c))) l (λ c h lh → Lg-rd₁ lW h (u ≤rf lW (toD c)) lh)
Lg-rd₁ {W} lW b (nκ _ u) l =
  Lg-nbA (λ c h → rd₁-fst (lwκ c (proj₁ lW) , tt) h (u (pwκ (proj₁ W) c) (lwκ c (proj₁ lW)))) l
         (λ c h lh → Lg-rd₁ (lwκ c (proj₁ lW) , tt) h (u (pwκ (proj₁ W) c) (lwκ c (proj₁ lW))) lh)
Lg-rd₁ lW b (nε κ zz u) l = ⊥-elim (ze1 κ zz)
Lg-rd₁ lW b (nw p x) l = Lg-rd₁ (lgW≤ p lW) b x l
Lg-rdp₁ lW b d l zero = l
Lg-rdp₁ lW b d l (suc n) = Lg-rd₁ lW (rdp₁ lW b d n) (d n) (Lg-rdp₁ lW b d l n)
```

## §3 第 2 层读成 `HB S₁`

`σA`, `σH`: `S₁ = step S₀` 的两个种类. κ₀ 闭包的坐标 $x$ 上的世界: 接一个 κ₀ 事件, 增量 `xε x`.

```agda
σA σH : K (step S₀)
σA = inj₁ tt
σH = inj₂ tt

xε : ∀ {W} → LgWε W → H₀ → H₀
xε {W} lW x = rd₁ lW hz (toD₁ {W} x)

lxε : ∀ {W} (lW : LgWε W) x → LgB (xε lW x)
lxε lW x = Lg-rd₁ lW hz (toD₁ x) tt

evx : ∀ {W} → LgWε W → H₀ → Ev
evx lW x = ev hz (hsuc hself) (xε lW x) (lxε lW x)

≤x : ∀ {W} (lW : LgWε W) x → W ≤ (proj₁ W , evx lW x ∷ proj₂ W)
≤x lW x = C.self , there (evx lW x) here

rd₂  : ∀ {W} → LgWε W → H₁ → D₂ W → H₁
rdp₂ : ∀ {W} → LgWε W → H₁ → (ℕ → D₂ W) → ℕ → H₁
rd₂ lW b n0 = b
rd₂ lW b n1 = hs b
rd₂ lW b (x ⨾ y) = rd₂ lW (rd₂ lW b x) y
rd₂ lW b (nl d) = hl (rdp₂ lW b d)
rd₂ lW b (ni (ss hself) u) = hΩ σH (nbᴮ b (λ x h → rd₂ lW h (u ≤rf lW (toD₁ x))))
rd₂ lW b (ni (ss (hsuc hself)) u) = hΩ σA (nbAᵗ b (λ c h → rd₂ lW h (u ≤rf lW (toD c))))
rd₂ {W} lW b (nκ _ u) =
  hΩ σA (nbAᵗ b (λ c h → rd₂ (lwκ c (proj₁ lW) , tt) h (u (pwκ (proj₁ W) c) (lwκ c (proj₁ lW)))))
rd₂ lW b (nε (_ , hsuc hself) zz u) =
  hΩ σH (nbᴮ b (λ x h → rd₂ (proj₁ lW , tt) h (u (≤x lW x) (proj₁ lW , tt))))
rd₂ lW b (nε (_ , hself) () u)
rd₂ lW b (nw p x) = rd₂ (lgW≤ p lW) b x
rdp₂ lW b d zero = b
rdp₂ lW b d (suc n) = rd₂ lW (rdp₂ lW b d n) (d n)

rd₂-fst : ∀ {W} (lW : LgWε W) b (x : D₂ W) {w} → b ⊲[ w ] rd₂ lW b x
rd₂-fst lW b n0 = hself
rd₂-fst lW b n1 = hsuc hself
rd₂-fst lW b (x ⨾ y) = ⊲ᴮ-tr (rd₂-fst lW b x) (rd₂-fst lW (rd₂ lW b x) y)
rd₂-fst lW b (nl d) = hlim 0 hself
rd₂-fst lW b (ni (ss hself) u) {w} = hLim {step S₀} {κ = σH} {c = hz} (z⊲ᴮ (proj₂ w)) hself
rd₂-fst lW b (ni (ss (hsuc hself)) u) {w} = hLim {step S₀} {κ = σA} {c = azero} (z⊲ (proj₁ w)) hself
rd₂-fst lW b (nκ _ u) {w} = hLim {step S₀} {κ = σA} {c = azero} (z⊲ (proj₁ w)) hself
rd₂-fst lW b (nε (_ , hsuc hself) zz u) {w} = hLim {step S₀} {κ = σH} {c = hz} (z⊲ᴮ (proj₂ w)) hself
rd₂-fst lW b (nε (_ , hself) () u)
rd₂-fst lW b (nw p x) = rd₂-fst (lgW≤ p lW) b x

Lg-rd₂  : ∀ {W} (lW : LgWε W) b (x : D₂ W) → LgB b → LgB (rd₂ lW b x)
Lg-rdp₂ : ∀ {W} (lW : LgWε W) b (d : ℕ → D₂ W) → LgB b → ∀ n → LgB (rdp₂ lW b d n)
Lg-rd₂ lW b n0 l = l
Lg-rd₂ lW b n1 l = l
Lg-rd₂ lW b (x ⨾ y) l = Lg-rd₂ lW (rd₂ lW b x) y (Lg-rd₂ lW b x l)
Lg-rd₂ lW b (nl d) l = (λ n → rd₂-fst lW (rdp₂ lW b d n) (d n)) , Lg-rdp₂ lW b d l
Lg-rd₂ lW b (ni (ss hself) u) l =
  cont→Lg (nb-contB l (λ x h → rd₂-fst lW h (u ≤rf lW (toD₁ x))) (λ x h lh → Lg-rd₂ lW h (u ≤rf lW (toD₁ x)) lh))
Lg-rd₂ lW b (ni (ss (hsuc hself)) u) l =
  Lg-nbAᵗ (λ c h → rd₂-fst lW h (u ≤rf lW (toD c))) l (λ c h lh → Lg-rd₂ lW h (u ≤rf lW (toD c)) lh)
Lg-rd₂ {W} lW b (nκ _ u) l =
  Lg-nbAᵗ (λ c h → rd₂-fst (lwκ c (proj₁ lW) , tt) h (u (pwκ (proj₁ W) c) (lwκ c (proj₁ lW)))) l
          (λ c h lh → Lg-rd₂ (lwκ c (proj₁ lW) , tt) h (u (pwκ (proj₁ W) c) (lwκ c (proj₁ lW))) lh)
Lg-rd₂ lW b (nε (_ , hsuc hself) zz u) l =
  cont→Lg (nb-contB l (λ x h → rd₂-fst (proj₁ lW , tt) h (u (≤x lW x) (proj₁ lW , tt)))
                      (λ x h lh → Lg-rd₂ (proj₁ lW , tt) h (u (≤x lW x) (proj₁ lW , tt)) lh))
Lg-rd₂ lW b (nε (_ , hself) () u) l
Lg-rd₂ lW b (nw p x) l = Lg-rd₂ (lgW≤ p lW) b x l
Lg-rdp₂ lW b d l zero = l
Lg-rdp₂ lW b d l (suc n) = Lg-rd₂ lW (rdp₂ lW b d n) (d n) (Lg-rdp₂ lW b d l n)
```

## §4 读回层与增量

```agda
RLay : Kᵉ → Ht
RLay (_ , hself) = hs (hs hz)
RLay (_ , hsuc hself) = hs hz

RB : ∀ κ {W} → LgWε W → D (RLay κ) W → Σ (HB (Lev (proj₁ κ))) LgB
RB (_ , hself) lW x = rd₂ lW hz x , Lg-rd₂ lW hz x tt
RB (_ , hsuc hself) lW x = rd₁ lW hz x , Lg-rd₁ lW hz x tt

-- 增量作为事件
evRB : ∀ κ {W} → LgWε W → D (RLay κ) W → Ev
evRB κ lW x = ev (proj₁ κ) (proj₂ κ) (proj₁ (RB κ lW x)) (proj₂ (RB κ lW x))
```

## §5 移植与丢掉事件

```agda
tp : ∀ {H′ X} → Suf H′ X → Hist → Hist
tp here H = H
tp (there e s) H = e ∷ tp s H

tp-suf : ∀ {H′ X} (s : Suf H′ X) H → Suf H (tp s H)
tp-suf here H = here
tp-suf (there e s) H = there e (tp-suf s H)

drp₁ : ∀ {a H H′} → D₁ (a , H) → D₁ (a , H′)
drp₁ n0 = n0
drp₁ n1 = n1
drp₁ (x ⨾ y) = drp₁ x ⨾ drp₁ y
drp₁ (nl d) = nl (λ n → drp₁ (d n))
drp₁ {H = H} (ni (ss hself) u) =
  ni (ss hself) (λ {W″} q lW″ z → drp₁ (u {proj₁ W″ , tp (proj₂ q) H} (proj₁ q , tp-suf (proj₂ q) H) (proj₁ lW″ , tt) (drp z)))
drp₁ (nκ zz u) = nκ zz (λ p lc → drp₁ (u p lc))
drp₁ (nε κ zz u) = ⊥-elim (ze1 κ zz)
drp₁ (nw p t) = nw (proj₁ p , here) (drp₁ t)

drp₂ : ∀ {a H H′} → D₂ (a , H) → D₂ (a , H′)
drp₂ n0 = n0
drp₂ n1 = n1
drp₂ (x ⨾ y) = drp₂ x ⨾ drp₂ y
drp₂ (nl d) = nl (λ n → drp₂ (d n))
drp₂ {H = H} (ni (ss hself) u) =
  ni (ss hself) (λ {W″} q lW″ z → drp₂ (u {proj₁ W″ , tp (proj₂ q) H} (proj₁ q , tp-suf (proj₂ q) H) (proj₁ lW″ , tt) (drp₁ z)))
drp₂ {H = H} (ni (ss (hsuc hself)) u) =
  ni (ss (hsuc hself)) (λ {W″} q lW″ z → drp₂ (u {proj₁ W″ , tp (proj₂ q) H} (proj₁ q , tp-suf (proj₂ q) H) (proj₁ lW″ , tt) (drp z)))
drp₂ (nκ zz u) = nκ zz (λ p lc → drp₂ (u p lc))
drp₂ {H = H} (nε (c , hsuc hself) zz u) =
  nε (c , hsuc hself) zz (λ {W″} q lW″ → drp₂ (u {proj₁ W″ , tp (proj₂ q) H} (proj₁ q , tp-suf (proj₂ q) H) (proj₁ lW″ , tt)))
drp₂ (nε (_ , hself) () u)
drp₂ (nw p t) = nw (proj₁ p , here) (drp₂ t)
```
