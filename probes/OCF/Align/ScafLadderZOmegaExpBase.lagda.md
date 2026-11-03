> **机械克隆.** 由 `OmegaExpBase` 经脚本复制, 只为把 `NF₁`, `Occ` 换成 [ScafLadderZStandardOmega](ScafLadderZStandardOmega.lagda.md), [ScafLadderZSystemOmega](ScafLadderZSystemOmega.lagda.md) 的版本; 见 [ScafLadder](ScafLadder.lagda.md). 下面的文字是原文.

# 树指数帧 $\Omega_\Omega\cdot\omega^\eta$: 续延式前缀栈与一般栈上的带前缀引理

> 接 [OmegaKBase](OmegaKBase.lagda.md) 与 [OmegaK](OmegaK.lagda.md) §4. 本文是 [OmegaExp](OmegaExp.lagda.md) 的前半: 折叠、记号、一般栈上的带前缀引理与 "好栈" 的三种构造. 决定性检验在 OmegaExp.
>
> 结论先说:
>
> 1. **栈是续延, 不带下标 (§2).** 前缀栈不再是数据 (`Vec (Frame ℓ) n`), 而是它在尾巴 $0$ 处的值, 作为对目标与环境层号多态的函数: `Stk = ∀ {i ℓ} → zero <ᴵ ℓ → i <ᴵ ℓ → Ordˢ i`, $S\,z\,p=\psi_i(S+0)$. 尾巴折叠 `ψˢ S` 对尾巴结构递归, 栈只是参数 (尾巴 $0$ 处调用 $S$), 规则 6 的链点在同一个 $S$ 上换目标. 帧都是 `Stk → Stk`: `S ▹Ω̂` ($+\Omega_\Omega$, 弹出为界 $i+1$ 的闭包, 与 Prefix `ψᴾ` 的紧界弹栈同式), `S ▹ω X` ($+\Omega_\Omega\cdot\omega^X$, $X$ 是第 0 层的符号树), `S ▹Ω̂²` ($+\Omega_\Omega\cdot\Omega_\Omega=\Omega_\Omega\cdot\omega^{\Omega_\Omega}$, 第三种帧: 弹出为闭包, 点处的指数是不可数的 $\Omega_\eta$). 指数折叠 `ψᵉ S` 对指数 $X$ 结构递归: $X=0$ 弹 $\hat\Omega$; $X=Y+1$ (第 0 层) 给 $\lim_m$ `rep S Y m` ($m$ 个 $\omega^Y$ 帧, `rep S Y (m+1) = rep S Y m ▹ω Y`); $X=\lim f$ 逐项; `limᵢ`/`up`/`ŝ`/`ĉᴸ` 与尾巴折叠同 (第 $\ge1$ 层的指数只作栈顶, 不入栈).
> 2. **停机度量是 (指数树, 重数) 的字典序, 栈没有下标 (§2).** `ψᵉ` 在指数上结构下降, `rep` 在重数 $m$ 上下降而指数不变, 环 `ψᵉ → rep → ψᵉ` 里指数严格下降; 栈的增长 (弹一个 $\omega^{Y+1}$ 帧得 $m$ 个 $\omega^Y$ 帧) 对检查器不可见, 因为从不对栈递归. 一次通过. OmegaK §4 的 `Vec` 否定 (栈长 $n+1\mapsto m+n$) 由此绕开: 检查器不再需要栈长下降.
> 3. **记号 (§1).** 前缀是任意项列表 `ps` (含空), 目标项 `πw w ps b` $=\psi_w(ps+b)$. OmegaKBase 的交换引理与 `repK`/`ωK`/`gtK`/`penK`/`H1K` 推广为 `cofΣ`/`predΣ`/`fsnΣ`/`fsTΣ`/`OccΣ` 与 `repW`/`ωW`/`gtW`/`penW`/`H1W`, 统一经 `onCons` 对 `ps` 分 `[]` 与 `x ∷ _` 两种.
> 4. **一般栈上的带前缀引理 (§3–§5).** 以 "栈在尾巴 $0$ 处带标签" 为假设: `HypW S ps` (目标 $w\ne0$, `LabL₊`)、`Hyp0 S ps` (目标 $0$, 证书与标签) 与自互模拟 `S ≈ˢ S`. 参数化模块 `PreW`/`Pre0` 给出 OmegaKBase §3–§4 全部引理在任意这样的栈上的版本 (`PreS₊`/`Pre0S₊` 等), 证明逐字, 弹栈子句换成假设.
> 5. **好栈 (§6).** `Goodˢ S ps` = 三个假设. `Good∅ : Goodˢ ∅ˢ []`; `GoodΩ : Goodˢ S ps → Goodˢ (S ▹Ω̂) (ps ++ [Ω_Ω])` (OmegaKBase 的 `popLK`/`pop0K`, 不再对帧数递归); **`GoodE : Goodˢ S ps → Lab0ᴸ X η → X ≅ˢ X → Goodˢ (S ▹ω X) (ps ++ [ψ_Ω(η)])`**, 对指数的标签推导递归, 后继情形经 `repGood` 对重数归纳. 于是由 $\hat\Omega$ 帧与带结构标签的可数指数帧堆成的每个栈都是好栈, 它在目标 $0$、尾巴 $0$ 处的计值树带标签 $\psi_0(\Omega_\Omega\cdot\omega^{\eta_1}+\cdots+\Omega_\Omega\cdot\omega^{\eta_r})$. `Goodᴸ`、`gc`、`forceᴸ`、`limᴸ`/`ĉᴸ-mk`、`fs-mono₁`、`LabL` 原样导入; `domᴸ` 换成任意前缀的 `domS` (证明同).
> 6. **边界.** 只有第 0 层的指数入栈. `ψᵉ` 在第 $\ge1$ 层遇到后继 $Y+1$ 时没有正确的帧, 子句给占位值 $\Omega_i$ (§2 读法, OmegaExp §4): 第 1 层的帧可经帧证据 `σ1 z` 搬运 (临时文件编译通过, 未接入); 第 $k\ge2$ 层的帧要带地板的栈, 且在目标 $<k-1$ 时紧界闭包的分支层号放不下它 (OmegaExp 的 `noSim2`).
>
> 全文 `--safe --without-K`, 无公设、无洞、无停机或正性编译指示. 只导入已有模块, 不改任何已有文件.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.ScafLadderZOmegaExpBase where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _++_; replicate)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong)
open import Data.List.Properties using (++-identityʳ; ++-assoc)

open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open Ord-Ord using (iter)
open import OCF.Align.Level
open import OCF.Align.Symbolic using (Mlev; σ1)
open import OCF.Align.ScafLadderZPrefix using (Z; ĉᴸ; Ord₊ˢ; Uˢ; Ordˢ; outˢ; intoˢ; out-intoˢ; toZ; Ωˢ; addˢ; _+ˢ_;
  z<suc; H1-pen; H1-fsT; trˢ; tr⁻ˢ)
import OCF.Align.EBO as E
open E using (T; PT; natT; fsn; fsT; cof; pred; c0; c1; cω; cΩ; Ωt; _<ᵀ_; γT; sucT; cmpᵀ; Cmp; lt; eq; gt;
              []<; hd<; tl<; lv<; ar<; cofA; cofψ0; cofψ₊) renaming (ψ to ψᵗ)
open import OCF.Align.Correspond using (Lab; l0; l1; lω; Lab-≅; cof-ne; fs-rep; fs-ω)
open import OCF.Align.Bachmann using (fs-gt; pen→<; gt→≤; clash)
open import OCF.Align.Closure using (Pen; fsT₊-pen′; lt→<)
open import OCF.Align.ScafLadderZStandardOmega using (NF₁; NF₁-pred; NF₁-fsn; walk; walkD; tO-desc-NF)
open import OCF.Align.Standard using (Desc; d₀; Ctbl; c[]; c∷)
open import OCF.Align.ScafLadderZSystemOmega using (Occ; oh; od; os; ot; oτ; TailOf; th; ts; occ<)
open import OCF.Align.Stage2 using (Ωᵗ; tO)
open import OCF.Align.ScafLadderZUniformS
open import OCF.Align.ScafLadderZStage2Label using (one⁰; Lab-oc)
open import OCF.Align.ScafLadderZDecoupleBase using (ΩΩ; ŝ-reflg)
open import OCF.Align.ScafLadderZDecouple using (Idx; lvI; Ilt; Ieq; kdI; kdI′; gtν; kdI[]; cofP)
open import OCF.Align.ScafLadderZGoodLBase
```

## §1 记号

**前缀.** `πw w ps b` $=\psi_w(ps+b)$, `ps` 任意 (空栈对应 `[]`). EBO 的 `cof`/`pred`/`fsn`/`fsT` 与 $\psi$ 的参数规则只在参数字面为 cons 时展开, `ps ++ (y ∷ ys)` 对抽象的 `ps` 卡住; `onCons` 把一个关于 "某个 cons 参数" 的事实搬到 `ps ++ (y ∷ ys)` 上. 下面每条记号引理都是 "Correspond/Bachmann/Closure/Prefix 的原引理 + `onCons` + 交换引理". `γW` 是规则 6 的链 (前缀在链点里), `γW-eq` 把它对上 EBO 的 `γT`; `1<π`: 参数非零的 $\psi_0$ 大于 $1$.

```agda
πw : T → T → T → T
πw w ps b = ψᵗ w (ps ++ b) ∷ []

onCons : (P : T → Set) → (∀ x xs → P (x ∷ xs)) → ∀ ps y ys → P (ps ++ (y ∷ ys))
onCons P h []       y ys = h y ys
onCons P h (x ∷ ps) y ys = h x (ps ++ (y ∷ ys))

cofΣ : ∀ ps y ys → cof (ps ++ (y ∷ ys)) ≡ cof (y ∷ ys)
cofΣ []           y ys = refl
cofΣ (x ∷ [])     y ys = refl
cofΣ (x ∷ x′ ∷ ps) y ys = cofΣ (x′ ∷ ps) y ys

predΣ : ∀ ps y ys → pred (ps ++ (y ∷ ys)) ≡ ps ++ pred (y ∷ ys)
predΣ []            y ys = refl
predΣ (x ∷ [])      y ys = refl
predΣ (x ∷ x′ ∷ ps) y ys = cong (x ∷_) (predΣ (x′ ∷ ps) y ys)

fsnΣ : ∀ ps y ys m → fsn (ps ++ (y ∷ ys)) m ≡ ps ++ fsn (y ∷ ys) m
fsnΣ []            y ys m = refl
fsnΣ (x ∷ [])      y ys m = refl
fsnΣ (x ∷ x′ ∷ ps) y ys m = cong (x ∷_) (fsnΣ (x′ ∷ ps) y ys m)

fsTΣ : ∀ ps y ys θ → fsT (ps ++ (y ∷ ys)) θ ≡ ps ++ fsT (y ∷ ys) θ
fsTΣ []            y ys θ = refl
fsTΣ (x ∷ [])      y ys θ = refl
fsTΣ (x ∷ x′ ∷ ps) y ys θ = cong (x ∷_) (fsTΣ (x′ ∷ ps) y ys θ)

OccΣ : ∀ {w a} ps → Occ w a → Occ w (ps ++ a)
OccΣ []       o = o
OccΣ (x ∷ ps) o = ot (OccΣ ps o)

cofW : ∀ w ps y ys → cof (πw w ps (y ∷ ys)) ≡ cofA w (cof (y ∷ ys))
cofW w []       y ys = refl
cofW w (x ∷ ps) y ys = cong (cofA w) (cofΣ (x ∷ ps) y ys)

repW : ∀ w ps y ys → cof (y ∷ ys) ≡ c1 → ∀ m → fsn (πw w ps (y ∷ ys)) m ≡ replicate m (ψᵗ w (ps ++ pred (y ∷ ys)))
repW w ps y ys c m =
  trans (onCons (λ a → cof a ≡ c1 → fsn (ψᵗ w a ∷ []) m ≡ replicate m (ψᵗ w (pred a))) (λ x xs c′ → fs-rep w x xs c′ m)
                ps y ys (trans (cofΣ ps y ys) c))
        (cong (λ t → replicate m (ψᵗ w t)) (predΣ ps y ys))

ωW : ∀ w ps y ys → cof (y ∷ ys) ≡ cω → ∀ m → fsn (πw w ps (y ∷ ys)) m ≡ πw w ps (fsn (y ∷ ys) m)
ωW w ps y ys c m =
  trans (onCons (λ a → cof a ≡ cω → fsn (ψᵗ w a ∷ []) m ≡ ψᵗ w (fsn a m) ∷ []) (λ x xs c′ → fs-ω w x xs c′ m)
                ps y ys (trans (cofΣ ps y ys) c))
        (cong (λ t → ψᵗ w t ∷ []) (fsnΣ ps y ys m))

γW : T → T → T → ℕ → T
γW ps a ν zero    = Ωt ν
γW ps a ν (suc m) = πw ν ps (fsT a (γW ps a ν m))

γW-eq : ∀ ps y ys ν m → γT (ps ++ (y ∷ ys)) ν m ≡ γW ps (y ∷ ys) ν m
γW-eq ps y ys ν zero    = refl
γW-eq ps y ys ν (suc m) =
  cong (λ t → ψᵗ ν t ∷ []) (trans (cong (fsT (ps ++ (y ∷ ys))) (γW-eq ps y ys ν m)) (fsTΣ ps y ys _))

gtW : ∀ w ps y ys ν → cof (y ∷ ys) ≡ cΩ ν → cmpᵀ (sucT ν) w ≡ gt → ∀ m →
      fsn (πw w ps (y ∷ ys)) m ≡ πw w ps (fsT (y ∷ ys) (γW ps (y ∷ ys) ν m))
gtW w ps y ys ν c em m =
  trans (onCons (λ a → cof a ≡ cΩ ν → fsn (ψᵗ w a ∷ []) m ≡ ψᵗ w (fsT a (γT a ν m)) ∷ [])
                (λ x xs c′ → fs-gt w x xs ν c′ em m) ps y ys (trans (cofΣ ps y ys) c))
        (cong (λ t → ψᵗ w t ∷ []) (trans (cong (fsT (ps ++ (y ∷ ys))) (γW-eq ps y ys ν m)) (fsTΣ ps y ys _)))

penW : ∀ w ps y ys ν → cof (y ∷ ys) ≡ cΩ ν → Pen (cmpᵀ (sucT ν) w) → ∀ η →
       fsT (πw w ps (y ∷ ys)) η ≡ πw w ps (fsT (y ∷ ys) η)
penW w ps y ys ν c pn η =
  trans (onCons (λ a → cof a ≡ cΩ ν → fsT (ψᵗ w a ∷ []) η ≡ ψᵗ w (fsT a η) ∷ [])
                (λ x xs c′ → fsT₊-pen′ w (x ∷ xs) ν (cof (x ∷ xs)) c′ pn η) ps y ys (trans (cofΣ ps y ys) c))
        (cong (λ t → ψᵗ w t ∷ []) (fsTΣ ps y ys η))

H1W : ∀ x xs ps y ys → cof (y ∷ ys) ≡ cΩ [] → ∀ θ → fsT (πw (x ∷ xs) ps (y ∷ ys)) θ ≡ πw (x ∷ xs) ps (fsT (y ∷ ys) θ)
H1W x xs ps y ys c θ =
  trans (onCons (λ a → cof a ≡ cΩ [] → fsT (ψᵗ (x ∷ xs) a ∷ []) θ ≡ ψᵗ (x ∷ xs) (fsT a θ) ∷ [])
                (λ v vs c′ → H1-fsT x xs v vs c′ θ) ps y ys (trans (cofΣ ps y ys) c))
        (cong (λ t → ψᵗ (x ∷ xs) t ∷ []) (fsTΣ ps y ys θ))

1<π : ∀ ps y ys → natT 1 <ᵀ πw [] ps (y ∷ ys)
1<π ps y ys = onCons (λ a → natT 1 <ᵀ ψᵗ [] a ∷ []) (λ x xs → lt→< (natT 1) (ψᵗ [] (x ∷ xs) ∷ []) refl) ps y ys
```

**读法.** 与 OmegaKBase §1 的区别只在前缀的形状: 那里是 `ΩΩ ∷ ΠΩ n b` (字面 cons, 对 $n$ 归纳), 这里是任意列表, 包括空列表 ($\psi_w(b)$, 空栈), 所以连 `cofW` 也要对 `ps` 分情形.

## §2 折叠

**栈与尾巴折叠.** `ψˢ S z p σ a` 表示 $\psi_i(S+a)$. 子句与 Prefix 的 `ψᴾ` 逐条相同, 只有尾巴 $0$ 换成 `S z p`; 帧证据 `z : zero <ᴵ ℓ` 随调用传递 (链点不换环境层号, $z$ 不变). `∅ˢ`: $\psi_i(0)=\Omega_i$. `S ▹Ω̂`: 弹出 $\hat\Omega$ 的闭包, 与 `ψᴾ (suc n) … (fΩ̂ z ∷ P) zero` 在纯 $\hat\Omega$ 栈时 (`rebase` 取紧界) 同式: 界 $i+1$, 第 0 点在环境层号 $i+1$ 上 (目标仍是 $i$, 证明 `zero : i <ᴵ suc i`, 尾巴 $\Omega_1$ 经 `σ1`), 分支在 `Mlev (suc i) η e` 上 (尾巴 $\Omega_\eta$ 经 `lim 1`), 剩余栈的帧证据分别是 `z<suc z p` 与 `lim 0 (z<suc z p)`. 与 Prefix 的区别: 剩余栈不需要重建, 它本来就对层号多态.

```agda
Stk : Set
Stk = ∀ {i ℓ} → zero <ᴵ ℓ → i <ᴵ ℓ → Ordˢ i

ψˢ : Stk → ∀ {i k ℓ} → zero <ᴵ ℓ → i <ᴵ ℓ → Simᴵ k ℓ → Ordˢ k → Ordˢ i
ψˢ S z p σ Ord₊ˢ.zero    = S z p
ψˢ S z p σ (Ord₊ˢ.suc a) = Ord₊ˢ.lim (iter (ψˢ S z p σ a +ˢ_) Ord₊ˢ.zero)
ψˢ S z p σ (Ord₊ˢ.lim f) = Ord₊ˢ.lim (λ m → ψˢ S z p σ (f m))
ψˢ S z p σ (Ord₊ˢ.limᵢ {i = j} q f) with <ᴵ-dec (σ q) p
... | injᵃ (via e r) = Ord₊ˢ.limᵢ r (λ y → ψˢ S z p σ (f (intoˢ (<→◃ q) (tr⁻ˢ e (outˢ (<→◃ r) y)))))
... | injᵇ _ = Ord₊ˢ.lim (λ m → ψˢ S z p σ (f (intoˢ (<→◃ q) (iter (λ x → ψˢ S z (σ q) σ (f (intoˢ (<→◃ q) x))) (Ωˢ j) m))))
... | injᶜ _ = Ord₊ˢ.lim (λ m → ψˢ S z p σ (f (intoˢ (<→◃ q) (iter (λ x → ψˢ S z (σ q) σ (f (intoˢ (<→◃ q) x))) (Ωˢ j) m))))
ψˢ S z p σ (Ord₊ˢ.up zero x)     = ψˢ S z p (λ q → σ (suc q)) x
ψˢ S z p σ (Ord₊ˢ.up (self m) x) = ψˢ S z p (λ q → σ (lim m q)) x
ψˢ S {k = zero}    z p σ (Ord₊ˢ.ŝ c t₀ g) = Ord₊ˢ.ĉᴸ c (toZ t₀) (λ η e → toZ (g η e)) (ψˢ S z p σ t₀) (λ η e → ψˢ S z p σ (g η e))
ψˢ S {k = suc _}   z p σ (Ord₊ˢ.ŝ c t₀ g) = Ord₊ˢ.ŝ c (ψˢ S z p σ t₀) (λ η e → ψˢ S z p σ (g η e))
ψˢ S {k = lim _ _} z p σ (Ord₊ˢ.ŝ c t₀ g) = Ord₊ˢ.ŝ c (ψˢ S z p σ t₀) (λ η e → ψˢ S z p σ (g η e))
ψˢ S z p σ (Ord₊ˢ.ĉᴸ c t₀ g o₀ o) = Ord₊ˢ.ĉᴸ c t₀ g (ψˢ S z p σ o₀) (λ η e → ψˢ S z p σ (o η e))

∅ˢ : Stk
∅ˢ {i} z p = Ωˢ i

_▹Ω̂ : Stk → Stk
(S ▹Ω̂) {i} z p =
  Ord₊ˢ.ŝ (suc i) (ψˢ S (z<suc z p) zero (σ1 (z<suc z p)) (Ωˢ (suc zero)))
          (λ η e → ψˢ S {ℓ = Mlev (suc i) η e} (lim 0 (z<suc z p)) (lim 0 zero) (λ q → lim 1 q) (Ωˢ η))
```

**读法.** `ψˢ` 的停机与 UniformS 的 `ψ0` 相同: 只对尾巴递归, 栈 $S$ 从不被分解.

**指数折叠.** `ψᵉ S z p σ X` 表示 $\psi_i(S+\Omega_\Omega\cdot\omega^X)$, $X$ 在第 $k$ 层, `σ : Simᴵ k ℓ`. EBO 里 $\Omega_\Omega\cdot\omega^\eta=\psi_\Omega(\eta)$ ($\eta$ 可数), 末项 $\psi_\Omega(\eta)$ 的基本列决定子句:

- $X=0$: $\psi_\Omega(0)=\Omega_\Omega$, 即 `(S ▹Ω̂) z p`.
- $X=Y+1$, 第 0 层: $\psi_\Omega(\eta+1)[m]=\psi_\Omega(\eta)\cdot m$ (规则 4), 所以 $\lim_m$ `rep S Y m z p`; `rep S Y m` $=S+\Omega_\Omega\cdot\omega^Y\cdot m$, `rep S Y (m+1) = rep S Y m ▹ω Y` (新帧在栈顶). 弹出 $\omega^{Y+1}$ 得 $m$ 个 $\omega^Y$, 帧数是基本列下标 $m$ (OmegaK §4).
- $X=\lim f$: $\psi_\Omega(\eta)[n]=\psi_\Omega(\eta[n])$ (规则 5ω).
- `limᵢ q f` (共尾度 $\Omega_{j+1}$): 可数的 $\nu$ 有 $\nu+1<\Omega$, $\psi_\Omega$ 穿透, $\Omega_\Omega\cdot\omega^X$ 的共尾度仍是 $\Omega_{j+1}$, 所以与尾巴的 `limᵢ` 子句同: 比较 $j$ 与目标 $i$, 穿透, 或沿第 $j$ 层的链折叠, 链点 $\psi_j(S+\Omega_\Omega\cdot\omega^{f\chi})$ 在同一个 $S$ 上.
- `up`/`ŝ`/`ĉᴸ`: 与尾巴同.
- $X=Y+1$, 第 $\ge1$ 层: **占位值** $\Omega_i$ (见下面的读法).

`σ⊥`: 第 0 层的 `Sim` 一律取这一个常量; 两处各自的 `λ ()` 不定义性相等, 否则 `rep S Y (m+1)` 与 `rep S Y m ▹ω Y` 对不上. `S ▹Ω̂²`: 指数 $\Omega_\Omega$ 的 $\Omega$-基本列 $[\eta]=\Omega_\eta$, 所以弹出与 `▹Ω̂` 同式, 第 0 点与分支是 `ψᵉ S` 作用于不可数指数 $\Omega_1$、$\Omega_\eta$ (它们只作栈顶).

```agda
σ⊥ : ∀ {ℓ} → Simᴵ zero ℓ
σ⊥ ()

ψᵉ : Stk → ∀ {i k ℓ} → zero <ᴵ ℓ → i <ᴵ ℓ → Simᴵ k ℓ → Ordˢ k → Ordˢ i
rep : Stk → Ordˢ zero → ℕ → Stk
_▹ω_ : Stk → Ordˢ zero → Stk

ψᵉ S z p σ Ord₊ˢ.zero = (S ▹Ω̂) z p
ψᵉ S {k = zero}    z p σ (Ord₊ˢ.suc a) = Ord₊ˢ.lim (λ m → rep S a m z p)
ψᵉ S {i} {k = suc _}   z p σ (Ord₊ˢ.suc a) = Ωˢ i
ψᵉ S {i} {k = lim _ _} z p σ (Ord₊ˢ.suc a) = Ωˢ i
ψᵉ S z p σ (Ord₊ˢ.lim f) = Ord₊ˢ.lim (λ m → ψᵉ S z p σ (f m))
ψᵉ S z p σ (Ord₊ˢ.limᵢ {i = j} q f) with <ᴵ-dec (σ q) p
... | injᵃ (via e r) = Ord₊ˢ.limᵢ r (λ y → ψᵉ S z p σ (f (intoˢ (<→◃ q) (tr⁻ˢ e (outˢ (<→◃ r) y)))))
... | injᵇ _ = Ord₊ˢ.lim (λ m → ψᵉ S z p σ (f (intoˢ (<→◃ q) (iter (λ x → ψᵉ S z (σ q) σ (f (intoˢ (<→◃ q) x))) (Ωˢ j) m))))
... | injᶜ _ = Ord₊ˢ.lim (λ m → ψᵉ S z p σ (f (intoˢ (<→◃ q) (iter (λ x → ψᵉ S z (σ q) σ (f (intoˢ (<→◃ q) x))) (Ωˢ j) m))))
ψᵉ S z p σ (Ord₊ˢ.up zero x)     = ψᵉ S z p (λ q → σ (suc q)) x
ψᵉ S z p σ (Ord₊ˢ.up (self m) x) = ψᵉ S z p (λ q → σ (lim m q)) x
ψᵉ S {k = zero}    z p σ (Ord₊ˢ.ŝ c t₀ g) = Ord₊ˢ.ĉᴸ c (toZ t₀) (λ η e → toZ (g η e)) (ψᵉ S z p σ t₀) (λ η e → ψᵉ S z p σ (g η e))
ψᵉ S {k = suc _}   z p σ (Ord₊ˢ.ŝ c t₀ g) = Ord₊ˢ.ŝ c (ψᵉ S z p σ t₀) (λ η e → ψᵉ S z p σ (g η e))
ψᵉ S {k = lim _ _} z p σ (Ord₊ˢ.ŝ c t₀ g) = Ord₊ˢ.ŝ c (ψᵉ S z p σ t₀) (λ η e → ψᵉ S z p σ (g η e))
ψᵉ S z p σ (Ord₊ˢ.ĉᴸ c t₀ g o₀ o) = Ord₊ˢ.ĉᴸ c t₀ g (ψᵉ S z p σ o₀) (λ η e → ψᵉ S z p σ (o η e))

(S ▹ω a) z p = ψᵉ S z p σ⊥ a

rep S a zero    = S
rep S a (suc m) = rep S a m ▹ω a

_▹Ω̂²  : Stk → Stk
(S ▹Ω̂²) {i} z p =
  Ord₊ˢ.ŝ (suc i) (ψᵉ S (z<suc z p) zero (σ1 (z<suc z p)) (Ωˢ (suc zero)))
          (λ η e → ψᵉ S {ℓ = Mlev (suc i) η e} (lim 0 (z<suc z p)) (lim 0 zero) (λ q → lim 1 q) (Ωˢ η))
```

**读法 (停机).** 一次通过, 栈不带任何下标. 调用图: `ψᵉ S … (suc Y)` → `rep S Y m` (指数从 $Y+1$ 降到 $Y$); `rep S Y (suc m)` → `rep S Y m` (重数降, 指数同) 与 `ψᵉ (rep S Y m) … Y` (指数同); 其余 `ψᵉ` 调用在指数的结构子项或 `f` 的值上. 检查器找到 (指数, 重数) 的字典序; 栈是第一个参数, 任意函数, 不参与度量. 对照 OmegaK §4 的两个编译结果: 以 `Vec` 长度为下标的 `ψᵛ` (弹 $\omega$ 帧时栈长 $n+1\mapsto m+n$) 失败; 计数器 `ψ²` 通过但只到 $\omega^2$. 这里计数器序列被嵌套的续延取代: 弹出 $\omega^{Y+1}$ 时新压的 $m$ 个 $\omega^Y$ 帧不是数据, 而是 `rep` 现造的函数, 它们的 "大小" 就是指数 $Y$, 而 $Y$ 是 `ψᵉ` 的递归参数.

**读法 (占位).** 第 $k\ge1$ 层的后继指数 $Y+1$ 要压 $\omega^Y$ 帧, 帧必须在以后每个环境层号 $\ell'$ 上都有 `Simᴵ k ℓ′`, 而多态的栈只带帧证据 $z:0<^\mathsf I\ell'$. $k=1$ 时 `σ1 z` 就是; 临时文件 `NegLv1.agda` (`(S ▹ω′ a) z p = ψᵉ S z p (σ1 z) a`, `a : Ordˢ (suc zero)`) 编译通过, `NegLv2.agda` (同一行, `a : Ordˢ (suc (suc zero))`) 报

    [UnequalTerms]
    (suc zero) != zero of type Ordᴵ
    when checking that the expression a has type Ordˢ (suc zero)

第 $k\ge2$ 层的帧若在目标 $\ge k-1$ 处产生 (穿透都如此), 改用带地板 $k\sqsubseteq^\mathsf I i$ 的栈即可 (目标只升不降); 若在更低的目标处产生, 紧界闭包的分支层号 `Mlev 1 1 e` 不含第 2 层 (OmegaExp §4 的 `noSim2`), 不是写法问题. 本文只给第 0 层的后继以正确子句; 本文与 OmegaExp 的一切标签定理都不经过占位子句 (`GoodE` 只收第 0 层的指数; OmegaExp 的 $\psi_0(\Omega_\Omega\cdot\Omega)$ 只在第 0 层的链点处计值).

## §3 互模拟

`S ≈ˢ S′`: 两个栈在一切 $\cong^\mathsf I$ 的目标处的值互模拟. `ψˢ-≅` 是 OmegaKBase `ψK-≅` 去掉弹栈递归 (尾巴 $0$ 处直接用假设), `lᵢ≅` 子句照 `liK` 把两个递归调用当 λ 传给 `liS` (OmegaKBase §2 记下了 `with` 写法的 `TerminationIssue`). `▹Ω̂-≈` 由 `ψˢ-≅`.

```agda
_≈ˢ_ : Stk → Stk → Set
S ≈ˢ S′ = ∀ {i i′ ℓ ℓ′} (z : zero <ᴵ ℓ) (p : i <ᴵ ℓ) (z′ : zero <ᴵ ℓ′) (p′ : i′ <ᴵ ℓ′) → i ≅ᴵ i′ → S z p ≅ˢ S′ z′ p′

liS : ∀ {S S′ : Stk} {i i′ k₁ ℓ₁ k₂ ℓ₂ j j′} {z : zero <ᴵ ℓ₁} {p : i <ᴵ ℓ₁} {σ : Simᴵ k₁ ℓ₁}
      {z′ : zero <ᴵ ℓ₂} {p′ : i′ <ᴵ ℓ₂} {σ′ : Simᴵ k₂ ℓ₂}
      {q : j <ᴵ k₁} {q′ : j′ <ᴵ k₂} {f : Uˢ j (<→◃ q) → Ordˢ k₁} {g : Uˢ j′ (<→◃ q′) → Ordˢ k₂} →
      i ≅ᴵ i′ → j ≅ᴵ j′ →
      (∀ (x : Ordˢ j) (y : Ordˢ j′) → Rˢ j (<→◃ q) (intoˢ (<→◃ q) x) y →
         ψˢ S z p σ (f (intoˢ (<→◃ q) x)) ≅ˢ ψˢ S′ z′ p′ σ′ (g (intoˢ (<→◃ q′) y))) →
      (∀ (x : Ordˢ j) (y : Ordˢ j′) → Rˢ j (<→◃ q) (intoˢ (<→◃ q) x) y →
         ψˢ S z (σ q) σ (f (intoˢ (<→◃ q) x)) ≅ˢ ψˢ S′ z′ (σ′ q′) σ′ (g (intoˢ (<→◃ q′) y))) →
      ψˢ S z p σ (Ord₊ˢ.limᵢ q f) ≅ˢ ψˢ S′ z′ p′ σ′ (Ord₊ˢ.limᵢ q′ g)
liS {S = S} {S′ = S′} {z = z} {p = p} {σ = σ} {z′ = z′} {p′ = p′} {σ′ = σ′} {q = q} {q′ = q′} {f = f} {g = g} ei e rec recC
  with <ᴵ-dec (σ q) p | <ᴵ-dec (σ′ q′) p′
... | injᵃ (via e₁ r₁) | injᵃ (via e₂ r₂) = lᵢ≅ (≅ᴵ-trans (≅ᴵ-sym e₁) (≅ᴵ-trans e e₂)) λ x y d →
  subst₂ (λ u v → ψˢ S z p σ (f (intoˢ (<→◃ q) (tr⁻ˢ e₁ u))) ≅ˢ ψˢ S′ z′ p′ σ′ (g (intoˢ (<→◃ q′) (tr⁻ˢ e₂ v))))
         (sym (out-intoˢ (<→◃ r₁) x)) (sym (out-intoˢ (<→◃ r₂) y))
         (rec _ _ (≅→Rˢ (<→◃ q) (tr⁻ˢ-≅ e₁ (≅-tr⁻ˢ e₂ (R→≅ˢ (<→◃ r₁) d)))))
... | injᵃ r | injᵇ s  = ⊥-elim (clash₁ e ei r s)
... | injᵃ r | injᶜ c  = ⊥-elim (clash₂ e ei r c)
... | injᵇ s | injᵃ r  = ⊥-elim (clash₁ (≅ᴵ-sym e) (≅ᴵ-sym ei) r s)
... | injᶜ c | injᵃ r  = ⊥-elim (clash₂ (≅ᴵ-sym e) (≅ᴵ-sym ei) r c)
... | injᵇ _ | injᵇ _  = l≅ (λ m → rec _ _ (≅→Rˢ (<→◃ q) (chain m)))
  where chain = iter-R _≅ˢ_ (λ d → recC _ _ (≅→Rˢ (<→◃ q) d)) (Ωˢ-≅ e)
... | injᵇ _ | injᶜ _  = l≅ (λ m → rec _ _ (≅→Rˢ (<→◃ q) (chain m)))
  where chain = iter-R _≅ˢ_ (λ d → recC _ _ (≅→Rˢ (<→◃ q) d)) (Ωˢ-≅ e)
... | injᶜ _ | injᵇ _  = l≅ (λ m → rec _ _ (≅→Rˢ (<→◃ q) (chain m)))
  where chain = iter-R _≅ˢ_ (λ d → recC _ _ (≅→Rˢ (<→◃ q) d)) (Ωˢ-≅ e)
... | injᶜ _ | injᶜ _  = l≅ (λ m → rec _ _ (≅→Rˢ (<→◃ q) (chain m)))
  where chain = iter-R _≅ˢ_ (λ d → recC _ _ (≅→Rˢ (<→◃ q) d)) (Ωˢ-≅ e)

ψˢ-≅ : ∀ {S S′ : Stk} → S ≈ˢ S′ → ∀ {i i′ k₁ ℓ₁ k₂ ℓ₂} {z : zero <ᴵ ℓ₁} {p : i <ᴵ ℓ₁} {σ : Simᴵ k₁ ℓ₁}
       {z′ : zero <ᴵ ℓ₂} {p′ : i′ <ᴵ ℓ₂} {σ′ : Simᴵ k₂ ℓ₂} {a : Ordˢ k₁} {b : Ordˢ k₂} →
       i ≅ᴵ i′ → a ≅ˢ b → ψˢ S z p σ a ≅ˢ ψˢ S′ z′ p′ σ′ b
ψˢ-≅ H {z = z} {p = p} {z′ = z′} {p′ = p′} ei z≅ = H z p z′ p′ ei
ψˢ-≅ H ei (s≅ e) = l≅ (iter-R _≅ˢ_ (λ e′ → addˢ-≅ (kd-≅ ei) (ψˢ-≅ H ei e) e′) z≅)
ψˢ-≅ H ei (l≅ h) = l≅ (λ n → ψˢ-≅ H ei (h n))
ψˢ-≅ H ei (upˡ {r = zero} e)   = ψˢ-≅ H ei e
ψˢ-≅ H ei (upˡ {r = self m} e) = ψˢ-≅ H ei e
ψˢ-≅ H ei (upʳ {r = zero} e)   = ψˢ-≅ H ei e
ψˢ-≅ H ei (upʳ {r = self m} e) = ψˢ-≅ H ei e
ψˢ-≅ H {k₁ = zero}    {k₂ = zero}    ei (ŝ≅ k ec et eg) =
  ĉ≅ ec (toZ-≅ et) (λ η e η′ e′ eη → toZ-≅ (eg η e η′ e′ eη)) (ψˢ-≅ H ei et) (λ η e η′ e′ eη → ψˢ-≅ H ei (eg η e η′ e′ eη))
ψˢ-≅ H {k₁ = zero}    {k₂ = suc _}   ei (ŝ≅ k ec et eg) = ⊥-elim (tf k)
ψˢ-≅ H {k₁ = zero}    {k₂ = lim _ _} ei (ŝ≅ k ec et eg) = ⊥-elim (tf k)
ψˢ-≅ H {k₁ = suc _}   {k₂ = zero}    ei (ŝ≅ k ec et eg) = ⊥-elim (tf (sym k))
ψˢ-≅ H {k₁ = lim _ _} {k₂ = zero}    ei (ŝ≅ k ec et eg) = ⊥-elim (tf (sym k))
ψˢ-≅ H {k₁ = suc _}   {k₂ = suc _}   ei (ŝ≅ k ec et eg) =
  ŝ≅ (kd-≅ ei) ec (ψˢ-≅ H ei et) (λ η e η′ e′ eη → ψˢ-≅ H ei (eg η e η′ e′ eη))
ψˢ-≅ H {k₁ = suc _}   {k₂ = lim _ _} ei (ŝ≅ k ec et eg) =
  ŝ≅ (kd-≅ ei) ec (ψˢ-≅ H ei et) (λ η e η′ e′ eη → ψˢ-≅ H ei (eg η e η′ e′ eη))
ψˢ-≅ H {k₁ = lim _ _} {k₂ = suc _}   ei (ŝ≅ k ec et eg) =
  ŝ≅ (kd-≅ ei) ec (ψˢ-≅ H ei et) (λ η e η′ e′ eη → ψˢ-≅ H ei (eg η e η′ e′ eη))
ψˢ-≅ H {k₁ = lim _ _} {k₂ = lim _ _} ei (ŝ≅ k ec et eg) =
  ŝ≅ (kd-≅ ei) ec (ψˢ-≅ H ei et) (λ η e η′ e′ eη → ψˢ-≅ H ei (eg η e η′ e′ eη))
ψˢ-≅ H ei (ĉ≅ ec dt dg eo eO) = ĉ≅ ec dt dg (ψˢ-≅ H ei eo) (λ η e η′ e′ eη → ψˢ-≅ H ei (eO η e η′ e′ eη))
ψˢ-≅ {S = S} {S′ = S′} H {z = z} {p = p} {σ = σ} {z′ = z′} {p′ = p′} {σ′ = σ′} ei (lᵢ≅ {p = q} {q = q′} {f = f} {g = g} e h) =
  liS {S = S} {S′ = S′} {z = z} {p = p} {σ = σ} {z′ = z′} {p′ = p′} {σ′ = σ′} {q = q} {q′ = q′} {f = f} {g = g} ei e
      (λ x y d → ψˢ-≅ H {z = z} {p = p} {σ = σ} {z′ = z′} {p′ = p′} {σ′ = σ′} ei (h x y d))
      (λ x y d → ψˢ-≅ H {z = z} {p = σ q} {σ = σ} {z′ = z′} {p′ = σ′ q′} {σ′ = σ′} e (h x y d))

∅-≈ : ∅ˢ ≈ˢ ∅ˢ
∅-≈ z p z′ p′ ei = Ωˢ-≅ ei

▹Ω̂-≈ : ∀ {S S′ : Stk} → S ≈ˢ S′ → (S ▹Ω̂) ≈ˢ (S′ ▹Ω̂)
▹Ω̂-≈ H z p z′ p′ ei = ŝ≅ (kd-≅ ei) (s≅ ei) (ψˢ-≅ H ei (Ωˢ-refl (suc zero))) (λ η e η′ e′ eη → ψˢ-≅ H ei (Ωˢ-≅ eη))
```

第 0 层指数: `ψᵉ0-≅`/`rep-≈` 对指数的互模拟推导与重数互递归. 推导 `ŝ≅` 的分支把**不同**的指数 $g\,\eta\,e$、$g\,\eta'\,e'$ 联系起来, 其下的后继给出不同的栈 `rep S a m`、`rep S′ b m`, 所以 `≈ˢ` 必须是二元的.

```agda
ψᵉ0-≅ : ∀ {S S′ : Stk} → S ≈ˢ S′ → ∀ {i i′ ℓ₁ ℓ₂} {z : zero <ᴵ ℓ₁} {p : i <ᴵ ℓ₁} {σ : Simᴵ zero ℓ₁}
        {z′ : zero <ᴵ ℓ₂} {p′ : i′ <ᴵ ℓ₂} {σ′ : Simᴵ zero ℓ₂} {a b : Ordˢ zero} →
        i ≅ᴵ i′ → a ≅ˢ b → ψᵉ S z p σ a ≅ˢ ψᵉ S′ z′ p′ σ′ b
rep-≈ : ∀ {S S′ : Stk} → S ≈ˢ S′ → ∀ {a b : Ordˢ zero} → a ≅ˢ b → ∀ m → rep S a m ≈ˢ rep S′ b m

ψᵉ0-≅ H {z = z} {p = p} {z′ = z′} {p′ = p′} ei z≅ = ▹Ω̂-≈ H z p z′ p′ ei
ψᵉ0-≅ H {z = z} {p = p} {z′ = z′} {p′ = p′} ei (s≅ e) = l≅ (λ m → rep-≈ H e m z p z′ p′ ei)
ψᵉ0-≅ H ei (l≅ h) = l≅ (λ n → ψᵉ0-≅ H ei (h n))
ψᵉ0-≅ H ei (lᵢ≅ {p = ()} e h)
ψᵉ0-≅ H ei (upˡ {r = ()} e)
ψᵉ0-≅ H ei (upʳ {r = ()} e)
ψᵉ0-≅ H ei (ŝ≅ k ec et eg) =
  ĉ≅ ec (toZ-≅ et) (λ η e η′ e′ eη → toZ-≅ (eg η e η′ e′ eη)) (ψᵉ0-≅ H ei et) (λ η e η′ e′ eη → ψᵉ0-≅ H ei (eg η e η′ e′ eη))
ψᵉ0-≅ H ei (ĉ≅ ec dt dg eo eO) = ĉ≅ ec dt dg (ψᵉ0-≅ H ei eo) (λ η e η′ e′ eη → ψᵉ0-≅ H ei (eO η e η′ e′ eη))

rep-≈ H e zero    = H
rep-≈ H e (suc m) z p z′ p′ ei = ψᵉ0-≅ (rep-≈ H e m) ei e

▹ω-≈ : ∀ {S S′ : Stk} → S ≈ˢ S′ → ∀ {a b : Ordˢ zero} → a ≅ˢ b → (S ▹ω a) ≈ˢ (S′ ▹ω b)
▹ω-≈ H e z p z′ p′ ei = ψᵉ0-≅ H ei e
```

**读法.** 用途: `liLabS` 的链原子要 $c_{m+1}\cong^\mathsf s c_{m+1}$, 由 `ψˢ-≅` 与栈的自互模拟 `S ≈ˢ S` 给出; 后者是好栈的第三个字段 (`▹Ω̂-≈`、`▹ω-≈` 逐层造出).

## §4 一般栈上的带前缀 $\psi_w$, 目标 $w\ne0$

`chainS`/`fold1S`/`pen1S`: OmegaKBase 的 `chainK`/`fold1K`/`pen1K` (证明不看栈). `HypW S ps`: 栈在尾巴 $0$、目标 $w\ne0$ 处带标签 $\psi_w(ps)$. 参数化模块 `PreW S ps H` 里的 `giPreS`/`PreAS`/`PreVS`/`PreS₊` 是 OmegaKBase 的 `giPreK`/`PreAK`/`PreVK`/`PreK₊` 逐字, 只换: `ψᴾ (suc n) p σ P` → `ψˢ S z p σ`; `ctxwK n w` → `πw w ps`; 记号引理 → §1 的 `…W`; `OccΠ (suc n)` → `OccΣ ps`; 弹栈 `popLK n` → `popW` (假设 `H`, 经 `++-identityʳ` 把 `ps` 对上 `ps ++ []`).

```agda
chainS : ∀ (S : Stk) {j k ℓ} (z : zero <ᴵ ℓ) (σ : Simᴵ k ℓ) (q : j <ᴵ k) (f : Uˢ j (<→◃ q) → Ordˢ k) → ℕ → Ordˢ j
chainS S {j} z σ q f = iter (λ x → ψˢ S z (σ q) σ (f (intoˢ (<→◃ q) x))) (Ωˢ j)

chainS-≅ : ∀ {S : Stk} {j k k′ ℓ} {z : zero <ᴵ ℓ} {σ : Simᴵ k ℓ} {q : j <ᴵ k} {f : Uˢ j (<→◃ q) → Ordˢ k} {b : Ordˢ k′} →
           S ≈ˢ S → Ord₊ˢ.limᵢ q f ≅ˢ b → ∀ m → chainS S z σ q f m ≅ˢ chainS S z σ q f m
chainS-≅ {j = j} H e zero    = Ωˢ-refl j
chainS-≅ {j = j} H e (suc m) = ψˢ-≅ H (≅ᴵ-refl j) (i-respˢ e (chainS-≅ H e m))

fold1S : ∀ {S : Stk} {i k ℓ j} {z : zero <ᴵ ℓ} {p : i <ᴵ ℓ} {σ : Simᴵ k ℓ} {q : j <ᴵ k} {f : Uˢ j (<→◃ q) → Ordˢ k} →
         (i ≺ᴵ j) ⊎ (i ≅ᴵ j) →
         ψˢ S z p σ (Ord₊ˢ.limᵢ q f) ≡ Ord₊ˢ.lim (λ m → ψˢ S z p σ (f (intoˢ (<→◃ q) (chainS S z σ q f m))))
fold1S {p = p} {σ = σ} {q = q} h with <ᴵ-dec (σ q) p
... | injᵃ s = ⊥-elim (clash s h)
... | injᵇ _ = refl
... | injᶜ _ = refl

pen1S : ∀ {S : Stk} {i k ℓ j N} {z : zero <ᴵ ℓ} {p : i <ᴵ ℓ} {σ : Simᴵ k ℓ} {q : j <ᴵ k} {f : Uˢ j (<→◃ q) → Ordˢ k} →
        j ≅ᴵ N → N ≺ᴵ i →
        Σ Ordᴵ λ j′ → Σ (j ≅ᴵ j′) λ e → Σ (j′ <ᴵ i) λ r →
        ψˢ S z p σ (Ord₊ˢ.limᵢ q f) ≡ Ord₊ˢ.limᵢ r (λ y → ψˢ S z p σ (f (intoˢ (<→◃ q) (tr⁻ˢ e (outˢ (<→◃ r) y)))))
pen1S {p = p} {σ = σ} {q = q} ej νi with <ᴵ-dec (σ q) p
... | injᵃ (via e r) = _ , e , r , refl
... | injᵇ s = ⊥-elim (≺ᴵ-irrefl (≺ᴵ-respʳ (≺ᴵ-trans νi s) ej))
... | injᶜ c = ⊥-elim (≺ᴵ-irrefl (≺ᴵ-respʳ νi (≅ᴵ-trans (≅ᴵ-sym c) ej)))

HypW : Stk → T → Set
HypW S ps = ∀ {i ℓ w} (z : zero <ᴵ ℓ) (p : i <ᴵ ℓ) (Iw : Idx w) → i ≅ᴵ lvI Iw → kd i ≡ false →
            LabL₊ i Ll (S z p) (ψᵗ w ps ∷ [])

ne-w : ∀ {i w} → (Iw : Idx w) → i ≅ᴵ lvI Iw → kd i ≡ false → w ≡ [] → ⊥
ne-w Iw ei ki refl = tf (trans (sym (kdI[] Iw)) (trans (sym (kd-≅ ei)) ki))

module PreW (S : Stk) (ps : T) (H : HypW S ps) where

  giPreS : ∀ {k ℓ i w ν j y ys} {z : zero <ᴵ ℓ} {p : i <ᴵ ℓ} {σ : Simᴵ k ℓ} {q : j <ᴵ k} {f : Uˢ j (<→◃ q) → Ordˢ k} →
           (Iw : Idx w) → i ≅ᴵ lvI Iw → kd i ≡ false → cof (y ∷ ys) ≡ cΩ ν → (Iν : Idx ν) → j ≅ᴵ lvI Iν →
           (rec : ∀ η (x : Ordˢ j) → LabL x η → LabL₊ i Ll (ψˢ S z p σ (f (intoˢ (<→◃ q) x))) (πw w ps (fsT (y ∷ ys) η))) →
           (recC : kd j ≡ false → ∀ η (x : Ordˢ j) → LabL x η →
                   LabL₊ j Ll (ψˢ S z (σ q) σ (f (intoˢ (<→◃ q) x))) (πw ν ps (fsT (y ∷ ys) η))) →
           LabL₊ i Ll (ψˢ S z p σ (Ord₊ˢ.limᵢ q f)) (πw w ps (y ∷ ys))
  giPreS {i = i} {w = w} {ν = ν} {j = j} {y = y} {ys = ys} {z = z} {p = p} {σ = σ} {q = q} {f = f} Iw ei ki c Iν ej rec recC =
    go (cmpᵀ (sucT ν) w) refl
    where
    pen : Pen (cmpᵀ (sucT ν) w) → LabL₊ i Ll (ψˢ S z p σ (Ord₊ˢ.limᵢ q f)) (πw w ps (y ∷ ys))
    pen pn with pen1S {S = S} {z = z} {p = p} {σ = σ} {q = q} {f = f} (≅ᴵ-refl j)
                      (≺ᴵ-respʳ (≺ᴵ-respˡ ej (Ilt Iν Iw (pen→< ν w pn))) (≅ᴵ-sym ei))
    ... | j′ , e , r , eqn =
      subst (λ W → LabL₊ i Ll W (πw w ps (y ∷ ys))) (sym eqn)
            (gi cofE Iν (≅ᴵ-trans (≅ᴵ-sym e) ej)
                (λ η x l → subst (λ v → LabL₊ i Ll (ψˢ S z p σ (f (intoˢ (<→◃ q) (tr⁻ˢ e v)))) (fsT (πw w ps (y ∷ ys)) η))
                                 (sym (out-intoˢ (<→◃ r) x))
                                 (subst (LabL₊ i Ll _) (sym (penW w ps y ys ν c pn η))
                                        (rec η (tr⁻ˢ e x) (LabL-tr⁻ e (Ll→ (<→◃ r) l))))))
      where
      cofE : cof (πw w ps (y ∷ ys)) ≡ cΩ ν
      cofE = trans (cofW w ps y ys) (trans (cong (cofA w) c) (cofP pn))
    fold : cmpᵀ (sucT ν) w ≡ gt → LabL₊ i Ll (ψˢ S z p σ (Ord₊ˢ.limᵢ q f)) (πw w ps (y ∷ ys))
    fold em =
      subst (λ W → LabL₊ i Ll W (πw w ps (y ∷ ys))) (sym (fold1S {S = S} {z = z} {p = p} {σ = σ} {q = q} {f = f} ij))
            (gl (trans (cofW w ps y ys) (trans (cong (cofA w) c) (cong (cofψ₊ w ν) em)))
                (λ m → subst (LabL₊ i Ll _) (sym (gtW w ps y ys ν c em m)) (rec _ _ (chainL m))))
      where
      gev : (lvI Iw ≺ᴵ lvI Iν) ⊎ (lvI Iw ≅ᴵ lvI Iν)
      gev with gt→≤ ν w em
      ... | inj₁ pw   = inj₁ (Ilt Iw Iν pw)
      ... | inj₂ refl = inj₂ (Ieq Iw Iν)
      ij : (i ≺ᴵ j) ⊎ (i ≅ᴵ j)
      ij with gev
      ... | inj₁ s  = inj₁ (≺ᴵ-respʳ (≺ᴵ-respˡ ei s) (≅ᴵ-sym ej))
      ... | inj₂ c′ = inj₂ (≅ᴵ-trans ei (≅ᴵ-trans c′ (≅ᴵ-sym ej)))
      kj : kd j ≡ false
      kj = trans (kd-≅ ej) (kdI′ Iν (gtν em (ne-w Iw ei ki)))
      chainL : ∀ m → LabL (chainS S z σ q f m) (γW ps (y ∷ ys) ν m)
      chainL zero    = LabL-Ω (proj₁ Iν) (proj₁ (proj₂ Iν)) (proj₁ (proj₂ (proj₂ Iν))) (proj₂ (proj₂ (proj₂ Iν))) ej
      chainL (suc m) = frL₊ kj (recC kj _ _ (chainL m))
    go : ∀ m → cmpᵀ (sucT ν) w ≡ m → LabL₊ i Ll (ψˢ S z p σ (Ord₊ˢ.limᵢ q f)) (πw w ps (y ∷ ys))
    go lt em = pen (inj₁ em)
    go eq em = pen (inj₂ em)
    go gt em = fold em

  popW : ∀ {i ℓ w} {z : zero <ᴵ ℓ} {p : i <ᴵ ℓ} (Iw : Idx w) → i ≅ᴵ lvI Iw → kd i ≡ false →
         LabL₊ i Ll (S z p) (πw w ps [])
  popW {i = i} {w = w} {z = z} {p = p} Iw ei ki =
    subst (λ t → LabL₊ i Ll (S z p) (ψᵗ w t ∷ [])) (sym (++-identityʳ ps)) (H z p Iw ei ki)

  PreAS : ∀ {ℓ i w} {z : zero <ᴵ ℓ} {p : i <ᴵ ℓ} {σ : Simᴵ zero ℓ} {X : Ordˢ zero} {b} →
          (Iw : Idx w) → i ≅ᴵ lvI Iw → kd i ≡ false → Lab0ᴸ X b → LabL₊ i Ll (ψˢ S z p σ X) (πw w ps b)
  PreVS : ∀ {k ℓ i w} {z : zero <ᴵ ℓ} {p : i <ᴵ ℓ} {σ : Simᴵ k ℓ} {X : Ordˢ k} {b} →
          (Iw : Idx w) → i ≅ᴵ lvI Iw → kd i ≡ false → LabL X b → LabL₊ i Ll (ψˢ S z p σ X) (πw w ps b)
  PreS₊ : ∀ {k ℓ i w} {z : zero <ᴵ ℓ} {p : i <ᴵ ℓ} {σ : Simᴵ k ℓ} {X : Ordˢ k} {b} →
          (Iw : Idx w) → i ≅ᴵ lvI Iw → kd i ≡ false → LabL₊ k Ll X b → LabL₊ i Ll (ψˢ S z p σ X) (πw w ps b)

  PreAS {z = z} {p = p} {b = []} Iw ei ki (lz c) = popW {z = z} {p = p} Iw ei ki
  PreAS {b = y ∷ ys} Iw ei ki (lz c) = ⊥-elim (cof-ne y ys c)
  PreAS {b = []} Iw ei ki (ls () l)
  PreAS {w = w} {z = z} {p = p} {σ = σ} {b = y ∷ ys} Iw ei ki (ls c l) =
    gl (trans (cofW w ps y ys) (cong (cofA w) c))
       (λ m → subst (LabL₊ _ Ll _) (sym (repW w ps y ys c m)) (LRep ki (PreAS {z = z} {p = p} {σ = σ} Iw ei ki l) m))
  PreAS {b = []} Iw ei ki (ll () h)
  PreAS {w = w} {z = z} {p = p} {σ = σ} {b = y ∷ ys} Iw ei ki (ll c h) =
    gl (trans (cofW w ps y ys) (cong (cofA w) c))
       (λ m → subst (LabL₊ _ Ll _) (sym (ωW w ps y ys c m)) (PreAS {z = z} {p = p} {σ = σ} Iw ei ki (h m)))
  PreAS {b = []} Iw ei ki (lŝ₀ () K h₀ hk)
  PreAS {w = w} {z = z} {p = p} {σ = σ} {b = y ∷ ys} Iw ei ki (lŝ₀ c K h₀ hk) =
    gĉ (trans (cofW w ps y ys) (cong (cofA w) c)) K
       (subst (LabL₊ _ Ll _) (sym (ωW w ps y ys c 0)) (PreAS {z = z} {p = p} {σ = σ} Iw ei ki h₀))
       (λ m → subst (LabL₊ _ Ll _) (sym (ωW w ps y ys c (suc m))) (PreAS {z = z} {p = p} {σ = σ} Iw ei ki (hk m)))
  PreAS {b = []} Iw ei ki (lĉ () K h₀ hk)
  PreAS {w = w} {z = z} {p = p} {σ = σ} {b = y ∷ ys} Iw ei ki (lĉ c K h₀ hk) =
    gĉ (trans (cofW w ps y ys) (cong (cofA w) c)) K
       (subst (LabL₊ _ Ll _) (sym (ωW w ps y ys c 0)) (PreAS {z = z} {p = p} {σ = σ} Iw ei ki h₀))
       (λ m → subst (LabL₊ _ Ll _) (sym (ωW w ps y ys c (suc m))) (PreAS {z = z} {p = p} {σ = σ} Iw ei ki (hk m)))

  PreVS {k = zero}    {z = z} {p = p} {σ = σ} Iw ei ki at = PreAS {z = z} {p = p} {σ = σ} Iw ei ki (atomL at)
  PreVS {k = suc _}   {z = z} {p = p} {σ = σ} Iw ei ki h  = PreS₊ {z = z} {p = p} {σ = σ} Iw ei ki h
  PreVS {k = lim _ _} {z = z} {p = p} {σ = σ} Iw ei ki h  = PreS₊ {z = z} {p = p} {σ = σ} Iw ei ki h

  PreS₊ {z = z} {p = p} {b = []} Iw ei ki (gz c) = popW {z = z} {p = p} Iw ei ki
  PreS₊ {b = y ∷ ys} Iw ei ki (gz c) = ⊥-elim (cof-ne y ys c)
  PreS₊ {b = []} Iw ei ki (gs () l)
  PreS₊ {w = w} {z = z} {p = p} {σ = σ} {b = y ∷ ys} Iw ei ki (gs c l) =
    gl (trans (cofW w ps y ys) (cong (cofA w) c))
       (λ m → subst (LabL₊ _ Ll _) (sym (repW w ps y ys c m)) (LRep ki (PreS₊ {z = z} {p = p} {σ = σ} Iw ei ki l) m))
  PreS₊ {b = []} Iw ei ki (gl () h)
  PreS₊ {w = w} {z = z} {p = p} {σ = σ} {b = y ∷ ys} Iw ei ki (gl c h) =
    gl (trans (cofW w ps y ys) (cong (cofA w) c))
       (λ m → subst (LabL₊ _ Ll _) (sym (ωW w ps y ys c m)) (PreS₊ {z = z} {p = p} {σ = σ} Iw ei ki (h m)))
  PreS₊ {z = z} {p = p} {σ = σ} Iw ei ki (gu {r = zero} h)   = PreVS {z = z} {p = p} {σ = λ q → σ (suc q)} Iw ei ki h
  PreS₊ {z = z} {p = p} {σ = σ} Iw ei ki (gu {r = self m} h) = PreVS {z = z} {p = p} {σ = λ q → σ (lim m q)} Iw ei ki h
  PreS₊ {b = []} Iw ei ki (gi () Iν ej h)
  PreS₊ {z = z} {p = p} {σ = σ} {b = y ∷ ys} Iw ei ki (gi {q = q} {f = f} c Iν ej h) =
    giPreS {z = z} {p = p} {σ = σ} {q = q} {f = f} Iw ei ki c Iν ej
           (λ η x l → PreS₊ {z = z} {p = p} {σ = σ} Iw ei ki (h η x (→Ll (<→◃ q) l)))
           (λ kj η x l → PreS₊ {z = z} {p = σ q} {σ = σ} Iν ej kj (h η x (→Ll (<→◃ q) l)))
  PreS₊ {b = []} Iw ei ki (gĉ () K h₀ hk)
  PreS₊ {w = w} {z = z} {p = p} {σ = σ} {b = y ∷ ys} Iw ei ki (gĉ c K h₀ hk) =
    gĉ (trans (cofW w ps y ys) (cong (cofA w) c)) K
       (subst (LabL₊ _ Ll _) (sym (ωW w ps y ys c 0)) (PreS₊ {z = z} {p = p} {σ = σ} Iw ei ki h₀))
       (λ m → subst (LabL₊ _ Ll _) (sym (ωW w ps y ys c (suc m))) (PreS₊ {z = z} {p = p} {σ = σ} Iw ei ki (hk m)))
  PreS₊ {k = zero} Iw ei ki (gŝ () c Ib bb ob h₀ hg)
  PreS₊ {k = suc _} {w = []} Iw ei ki (gŝ kk c Ib bb ob h₀ hg) = ⊥-elim (ne-w Iw ei ki refl)
  PreS₊ {k = suc _} {w = x ∷ xs} {b = []} Iw ei ki (gŝ kk () Ib bb ob h₀ hg)
  PreS₊ {k = suc _} {w = x ∷ xs} {z = z} {p = p} {σ = σ} {b = y ∷ ys} Iw ei ki (gŝ kk c Ib bb ob h₀ hg) =
    gŝ ki (trans (cofW (x ∷ xs) ps y ys) (trans (cong (cofA (x ∷ xs)) c) (H1-pen x xs))) Ib bb
       (λ θ → subst (Occ _) (sym (H1W x xs ps y ys c θ)) (od (OccΣ ps (ob θ))))
       (subst (LabL₊ _ Ll _) (sym (H1W x xs ps y ys c (natT 1))) (PreS₊ {z = z} {p = p} {σ = σ} Iw ei ki h₀))
       (λ θ Y hY lY nθ lt e → subst (LabL₊ _ Ll _) (sym (H1W x xs ps y ys c θ))
                                    (PreS₊ {z = z} {p = p} {σ = σ} Iw ei ki (hg θ Y hY lY nθ lt e)))
  PreS₊ {k = lim _ _} {w = []} Iw ei ki (gŝ kk c Ib bb ob h₀ hg) = ⊥-elim (ne-w Iw ei ki refl)
  PreS₊ {k = lim _ _} {w = x ∷ xs} {b = []} Iw ei ki (gŝ kk () Ib bb ob h₀ hg)
  PreS₊ {k = lim _ _} {w = x ∷ xs} {z = z} {p = p} {σ = σ} {b = y ∷ ys} Iw ei ki (gŝ kk c Ib bb ob h₀ hg) =
    gŝ ki (trans (cofW (x ∷ xs) ps y ys) (trans (cong (cofA (x ∷ xs)) c) (H1-pen x xs))) Ib bb
       (λ θ → subst (Occ _) (sym (H1W x xs ps y ys c θ)) (od (OccΣ ps (ob θ))))
       (subst (LabL₊ _ Ll _) (sym (H1W x xs ps y ys c (natT 1))) (PreS₊ {z = z} {p = p} {σ = σ} Iw ei ki h₀))
       (λ θ Y hY lY nθ lt e → subst (LabL₊ _ Ll _) (sym (H1W x xs ps y ys c θ))
                                    (PreS₊ {z = z} {p = p} {σ = σ} Iw ei ki (hg θ Y hY lY nθ lt e)))
```

**读法.** 停机一次通过, 递归只在尾巴的 `LabL₊` 推导上, 栈不动. OmegaKBase 里唯一的帧数下降 (`popLK (suc m)` 调 `PreVK m`) 移到 §6 的 `GoodΩ`, 那里不再递归.

## §5 一般栈上的带前缀 $\psi_0$: 证书与标签一起

`Hyp0 S ps`: 目标 $0$、尾巴 $0$ 处的证书与标签 $\psi_0(ps)$ (给定 `NF₁`). `domS`: GoodLBase `domᴸ` 的任意前缀版 (出现经 `od (OccΣ ps o)` 包进 $\psi_0$ 的参数), 证明同. `1<γ`: `gŝ` 行的分支要 $1<\theta$; OmegaKBase 用 `1<ctx` (参数字面以 $\Omega_\Omega$ 开头), 这里前缀可空, 改由 "`fsT` 的值非空" (`fsT-ne`; 要 $\Omega_1$-共尾, 以排除哑值 `fsT (𝟏 ∷ []) = []`) 与 `++-ne` 得到.

```agda
Hyp0 : Stk → T → Set
Hyp0 S ps = ∀ {L} (z : zero <ᴵ L) (p : zero <ᴵ L) → NF₁ (ψᵗ [] ps ∷ []) →
            Σ (Goodᴸ (toZ (S z p))) λ G → Lab (forceᴸ _ G) (ψᵗ [] ps ∷ [])

domS : ∀ {c w b Y} ps (hY : HS Y) (Iw : Idx w) → c ⊑ᴵ suc (lvI Iw) → Occ w b → Lab Y (πw [] ps b) → NF₁ (πw [] ps b) →
       c ⊑ᴵ toLevel Y hY
domS ps hY (W , hW , lW , nW) bw o lY nb =
  ⊑ᴵ-trans bw (s⊑′ (toLevel-≺ hW hY (Lab-oc lY nb lW nW (occ< nb (c∷ c[]) (od (OccΣ ps o)) (Lab→Ctbl lW nW)))))

1<ψ : ∀ b → (b ≡ [] → ⊥) → natT 1 <ᵀ ψᵗ [] b ∷ []
1<ψ []       ne = ⊥-elim (ne refl)
1<ψ (v ∷ vs) ne = lt→< (natT 1) (ψᵗ [] (v ∷ vs) ∷ []) refl

++-ne : ∀ ps {b : T} → (b ≡ [] → ⊥) → ps ++ b ≡ [] → ⊥
++-ne []       ne e = ne e
++-ne (x ∷ ps) ne ()

fsT0-ne : ∀ w ws c θ → (θ ≡ [] → ⊥) → E.fsT0 (w ∷ ws) c θ ≡ [] → ⊥
fsT0-ne w ws c0     θ ne ()
fsT0-ne w ws c1     θ ne e = ne e
fsT0-ne w ws cω     θ ne ()
fsT0-ne w ws (cΩ ν) θ ne ()

fsTc-ne : ∀ u b ν m θ → E.fsTc u b ν m θ ≡ [] → ⊥
fsTc-ne u b ν lt θ ()
fsTc-ne u b ν eq θ ()
fsTc-ne u b ν gt θ ()

fsT₊-ne : ∀ u b c θ → E.fsT₊ u b c θ ≡ [] → ⊥
fsT₊-ne u b c0     θ ()
fsT₊-ne u b c1     θ ()
fsT₊-ne u b cω     θ ()
fsT₊-ne u b (cΩ ν) θ e = fsTc-ne u b ν (cmpᵀ (sucT ν) u) θ e

fsT-ne : ∀ y ys θ → cof (y ∷ ys) ≡ cΩ [] → (θ ≡ [] → ⊥) → fsT (y ∷ ys) θ ≡ [] → ⊥
fsT-ne y (v ∷ vs) θ c ne ()
fsT-ne (ψᵗ u (v ∷ vs)) [] θ c ne e = fsT₊-ne u (v ∷ vs) (cof (v ∷ vs)) θ e
fsT-ne (ψᵗ (w ∷ ws) []) [] θ c ne e = fsT0-ne w ws (cof (w ∷ ws)) θ ne e
fsT-ne (ψᵗ [] []) [] θ () ne e

γW-ne : ∀ ps a ν m → γW ps a ν m ≡ [] → ⊥
γW-ne ps a ν zero    ()
γW-ne ps a ν (suc m) ()

1<γ : ∀ ps y ys → cof (y ∷ ys) ≡ cΩ [] → ∀ m → natT 1 <ᵀ γW ps (y ∷ ys) [] (suc m)
1<γ ps y ys c m = 1<ψ (ps ++ fsT (y ∷ ys) (γW ps (y ∷ ys) [] m)) (++-ne ps (fsT-ne y ys _ c (γW-ne ps (y ∷ ys) [] m)))
```

`Pre0 S ps HW H0 HR`: OmegaKBase §4 逐字. `liLabK` → `liLabS` (原子的自互模拟用 `ψˢ-≅ HR`); `foldLabK` → `foldLabS` (链点用 `PreS₊`); `ŝChainK` → `ŝChainS` (支配用 `domS`); `pop0K` → `pop0` (假设 `H0`).

```agda
module Pre0 (S : Stk) (ps : T) (HW : HypW S ps) (H0 : Hyp0 S ps) (HR : S ≈ˢ S) where
  open PreW S ps HW

  cofω : ∀ {y ys} → cof (y ∷ ys) ≡ cΩ [] → cof (πw [] ps (y ∷ ys)) ≡ cω
  cofω {y} {ys} c = trans (cofW [] ps y ys) (cong (cofA []) c)

  cofω′ : ∀ {y ys} → cof (y ∷ ys) ≡ cω → cof (πw [] ps (y ∷ ys)) ≡ cω
  cofω′ {y} {ys} c = trans (cofW [] ps y ys) (cong (cofA []) c)

  nfγ : ∀ {y ys} → NF₁ (πw [] ps (y ∷ ys)) → (c : cof (y ∷ ys) ≡ cΩ []) → ∀ m →
        NF₁ (πw [] ps (fsT (y ∷ ys) (γW ps (y ∷ ys) [] m)))
  nfγ {y} {ys} nu c m = subst NF₁ (gtW [] ps y ys [] c refl m) (NF₁-fsn nu (cofω c) m)

  nfω : ∀ {y ys} → NF₁ (πw [] ps (y ∷ ys)) → (c : cof (y ∷ ys) ≡ cω) → ∀ m → NF₁ (πw [] ps (fsn (y ∷ ys) m))
  nfω {y} {ys} nu c m = subst NF₁ (ωW [] ps y ys c m) (NF₁-fsn nu (cofω′ c) m)

  liLabS : ∀ {L k} {z p : zero <ᴵ L} {σ : Simᴵ k L} {q : zero <ᴵ k} {f : Uˢ zero (<→◃ q) → Ordˢ k} {y ys} →
           cof (y ∷ ys) ≡ cΩ [] → Ord₊ˢ.limᵢ q f ≅ˢ Ord₊ˢ.limᵢ q f → NF₁ (πw [] ps (y ∷ ys)) →
           (rec : ∀ (p′ : zero <ᴵ L) θ (x : Ordˢ zero) → Atomᴸ x θ → f (intoˢ (<→◃ q) x) ≅ˢ f (intoˢ (<→◃ q) x) →
                  NF₁ (πw [] ps (fsT (y ∷ ys) θ)) →
                  Σ (Goodᴸ (toZ (ψˢ S z p′ σ (f (intoˢ (<→◃ q) x))))) λ G → Lab (forceᴸ _ G) (πw [] ps (fsT (y ∷ ys) θ))) →
           Σ (Goodᴸ (toZ (ψˢ S z p σ (Ord₊ˢ.limᵢ q f)))) λ G → Lab (forceᴸ _ G) (πw [] ps (y ∷ ys))
  liLabS {z = z} {p = p} {σ = σ} {q = q} {f = f} {y = y} {ys = ys} c ex nu rec =
    subst (λ W → Σ (Goodᴸ (toZ W)) λ G → Lab (forceᴸ _ G) (πw [] ps (y ∷ ys))) (sym eqf)
          (limᴸ nu (cofω c) (λ m → proj₁ (outp m))
                (λ m → subst (Lab _) (sym (gtW [] ps y ys [] c refl m)) (proj₂ (outp m))))
    where
    eqf = fold1S {S = S} {z = z} {p = p} {σ = σ} {q = q} {f = f} (inj₂ z≅)
    atm : ∀ m → Atomᴸ (chainS S z σ q f m) (γW ps (y ∷ ys) [] m)
    atm zero    = Ωˢ-refl zero , gs gz , l1 refl (s≅ z≅) (l0 refl z≅)
    atm (suc m) = ψˢ-≅ HR {z = z} {p = σ q} {σ = σ} {z′ = z} {p′ = σ q} {σ′ = σ} z≅ (i-respˢ ex (proj₁ (atm m))) ,
                  rec (σ q) _ _ (atm m) (i-respˢ ex (proj₁ (atm m))) (nfγ nu c m)
    outp : ∀ m → Σ (Goodᴸ (toZ (ψˢ S z p σ (f (intoˢ (<→◃ q) (chainS S z σ q f m)))))) λ G →
                Lab (forceᴸ _ G) (πw [] ps (fsT (y ∷ ys) (γW ps (y ∷ ys) [] m)))
    outp m = rec p _ _ (atm m) (i-respˢ ex (proj₁ (atm m))) (nfγ nu c m)

  foldLabS : ∀ {L k j y ys v vs} {z p : zero <ᴵ L} {σ : Simᴵ k L} {q : j <ᴵ k} {f : Uˢ j (<→◃ q) → Ordˢ k} →
             cof (y ∷ ys) ≡ cΩ (v ∷ vs) → (I : Idx (v ∷ vs)) → j ≅ᴵ lvI I → kd j ≡ false →
             Ord₊ˢ.limᵢ q f ≅ˢ Ord₊ˢ.limᵢ q f → NF₁ (πw [] ps (y ∷ ys)) →
             (h : ∀ η (x : Ordˢ j) → LabL x η → LabL₊ k Ll (f (intoˢ (<→◃ q) x)) (fsT (y ∷ ys) η)) →
             (rec : ∀ η (x : Ordˢ j) → LabL x η → f (intoˢ (<→◃ q) x) ≅ˢ f (intoˢ (<→◃ q) x) →
                    NF₁ (πw [] ps (fsT (y ∷ ys) η)) →
                    Σ (Goodᴸ (toZ (ψˢ S z p σ (f (intoˢ (<→◃ q) x))))) λ G → Lab (forceᴸ _ G) (πw [] ps (fsT (y ∷ ys) η))) →
             Σ (Goodᴸ (toZ (ψˢ S z p σ (Ord₊ˢ.limᵢ q f)))) λ G → Lab (forceᴸ _ G) (πw [] ps (y ∷ ys))
  foldLabS {y = y} {ys = ys} {v = v} {vs = vs} {z = z} {p = p} {σ = σ} {q = q} {f = f} c I ej kj ex nu h rec =
    subst (λ W → Σ (Goodᴸ (toZ W)) λ G → Lab (forceᴸ _ G) (πw [] ps (y ∷ ys))) (sym eqf)
          (limᴸ nu cω′ (λ m → proj₁ (outp m))
                (λ m → subst (Lab _) (sym (gtW [] ps y ys (v ∷ vs) c refl m)) (proj₂ (outp m))))
    where
    cω′ : cof (πw [] ps (y ∷ ys)) ≡ cω
    cω′ = trans (cofW [] ps y ys) (cong (cofA []) c)
    eqf = fold1S {S = S} {z = z} {p = p} {σ = σ} {q = q} {f = f} (inj₁ (z≺I I ej (λ ())))
    chainL : ∀ m → LabL (chainS S z σ q f m) (γW ps (y ∷ ys) (v ∷ vs) m)
    chainL zero    = LabL-Ω (proj₁ I) (proj₁ (proj₂ I)) (proj₁ (proj₂ (proj₂ I))) (proj₂ (proj₂ (proj₂ I))) ej
    chainL (suc m) = frL₊ kj (PreS₊ {z = z} {p = σ q} {σ = σ} I ej kj (h _ _ (chainL m)))
    nf : ∀ m → NF₁ (πw [] ps (fsT (y ∷ ys) (γW ps (y ∷ ys) (v ∷ vs) m)))
    nf m = subst NF₁ (gtW [] ps y ys (v ∷ vs) c refl m) (NF₁-fsn nu cω′ m)
    outp : ∀ m → Σ (Goodᴸ (toZ (ψˢ S z p σ (f (intoˢ (<→◃ q) (chainS S z σ q f m)))))) λ G →
                Lab (forceᴸ _ G) (πw [] ps (fsT (y ∷ ys) (γW ps (y ∷ ys) (v ∷ vs) m)))
    outp m = rec _ _ (chainL m) (i-respˢ ex (chainS-≅ HR ex m)) (nf m)

  ŝChainS : ∀ {L k c w} {z p : zero <ᴵ L} {σ : Simᴵ k L} {t₀ : Ordˢ k} {g : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ k} {y ys} →
            cof (y ∷ ys) ≡ cΩ [] → NF₁ (πw [] ps (y ∷ ys)) → (Iw : Idx w) → c ⊑ᴵ suc (lvI Iw) → (∀ θ → Occ w (fsT (y ∷ ys) θ)) →
            (rec₀ : Σ (Goodᴸ (toZ (ψˢ S z p σ t₀))) λ G → Lab (forceᴸ _ G) (γW ps (y ∷ ys) [] 1)) →
            (rec : ∀ m Y (hY : HS Y) → Lab Y (γW ps (y ∷ ys) [] (suc m)) → (e : c ⊑ᴵ toLevel Y hY) →
                   Σ (Goodᴸ (toZ (ψˢ S z p σ (g (toLevel Y hY) e)))) λ G → Lab (forceᴸ _ G) (γW ps (y ∷ ys) [] (suc (suc m)))) →
            Σ (Goodᴸ (ĉᴸ c (toZ (ψˢ S z p σ t₀)) (λ η e → toZ (ψˢ S z p σ (g η e)))
                           (toZ (ψˢ S z p σ t₀)) (λ η e → toZ (ψˢ S z p σ (g η e))))) λ G →
              Lab (forceᴸ _ G) (πw [] ps (y ∷ ys))
  ŝChainS {y = y} {ys = ys} c nu Iw bw ow rec₀ rec =
    ĉᴸ-mk nu (cofω c) K (proj₁ rec₀) (subst (Lab _) (sym (gtW [] ps y ys [] c refl 0)) (proj₂ rec₀))
          (λ k → CCᴸ.Gg K k (Ptᴸ.x (ptK K k)) (Ptᴸ.hx (ptK K k)) (Ptᴸ.lx (ptK K k)) (Ptᴸ.dx (ptK K k)))
          (λ k → subst (Lab _) (sym (gtW [] ps y ys [] c refl (suc k)))
                       (CCᴸ.lE K k (Ptᴸ.x (ptK K k)) (Ptᴸ.hx (ptK K k)) (Ptᴸ.lx (ptK K k)) (Ptᴸ.dx (ptK K k))))
    where
    K = ccᴸ (λ m → γW ps (y ∷ ys) [] (suc m)) (proj₁ rec₀) (proj₂ rec₀)
            (domS ps _ Iw bw (ow (natT 1)) (proj₂ rec₀) (nfγ nu c 0))
            (λ m Y hY lY e → proj₁ (rec m Y hY lY e)) (λ m Y hY lY e → proj₂ (rec m Y hY lY e))
            (λ m Y hY lY e → domS ps _ Iw bw (ow (γW ps (y ∷ ys) [] (suc m))) (proj₂ (rec m Y hY lY e)) (nfγ nu c (suc m)))

  pop0 : ∀ {L} {z p : zero <ᴵ L} → NF₁ (πw [] ps []) → Σ (Goodᴸ (toZ (S z p))) λ G → Lab (forceᴸ _ G) (πw [] ps [])
  pop0 {z = z} {p = p} nu =
    subst (λ t → Σ (Goodᴸ (toZ (S z p))) λ G → Lab (forceᴸ _ G) (ψᵗ [] t ∷ [])) (sym (++-identityʳ ps))
          (H0 z p (subst (λ t → NF₁ (ψᵗ [] t ∷ [])) (++-identityʳ ps) nu))

  Pre0AS : ∀ {L} {z p : zero <ᴵ L} {σ : Simᴵ zero L} {x : Ordˢ zero} {a} →
           Lab0ᴸ x a → x ≅ˢ x → NF₁ (πw [] ps a) → Σ (Goodᴸ (toZ (ψˢ S z p σ x))) λ G → Lab (forceᴸ _ G) (πw [] ps a)
  Pre0VS : ∀ {L k} {z p : zero <ᴵ L} {σ : Simᴵ k L} {x : Ordˢ k} {a} →
           LabL x a → x ≅ˢ x → NF₁ (πw [] ps a) → Σ (Goodᴸ (toZ (ψˢ S z p σ x))) λ G → Lab (forceᴸ _ G) (πw [] ps a)
  Pre0S₊ : ∀ {L k} {z p : zero <ᴵ L} {σ : Simᴵ k L} {x : Ordˢ k} {a} →
           LabL₊ k Ll x a → x ≅ˢ x → NF₁ (πw [] ps a) → Σ (Goodᴸ (toZ (ψˢ S z p σ x))) λ G → Lab (forceᴸ _ G) (πw [] ps a)

  Pre0AS {z = z} {p = p} {a = []} (lz c) ex nu = pop0 {z = z} {p = p} nu
  Pre0AS {a = y ∷ ys} (lz c) ex nu = ⊥-elim (cof-ne y ys c)
  Pre0AS {a = []} (ls () l) ex nu
  Pre0AS {z = z} {p = p} {σ = σ} {a = y ∷ ys} (ls c l) ex nu =
    limᴸ nu cω′ (λ m → proj₁ (Rs m)) (λ m → subst (Lab _) (sym (repW [] ps y ys c m)) (proj₂ (Rs m)))
    where
    cω′ = trans (cofW [] ps y ys) (cong (cofA []) c)
    Rp = Pre0AS {z = z} {p = p} {σ = σ} l (s-invˢ ex) (subst NF₁ (repW [] ps y ys c 1) (NF₁-fsn nu cω′ 1))
    Rs = repᴸ (proj₁ Rp) (proj₂ Rp) (λ m → subst NF₁ (repW [] ps y ys c m) (NF₁-fsn nu cω′ m))
  Pre0AS {a = []} (ll () h) ex nu
  Pre0AS {z = z} {p = p} {σ = σ} {a = y ∷ ys} (ll c h) ex nu =
    limᴸ nu (cofω′ c)
         (λ m → proj₁ (Pre0AS {z = z} {p = p} {σ = σ} (h m) (l-invˢ ex m) (nfω nu c m)))
         (λ m → subst (Lab _) (sym (ωW [] ps y ys c m)) (proj₂ (Pre0AS {z = z} {p = p} {σ = σ} (h m) (l-invˢ ex m) (nfω nu c m))))
  Pre0AS {a = []} (lŝ₀ () K h₀ hk) ex nu
  Pre0AS {z = z} {p = p} {σ = σ} {a = y ∷ ys} (lŝ₀ c K h₀ hk) ex nu =
    ĉᴸ-mk nu (cofω′ c) K (proj₁ R₀) (subst (Lab _) (sym (ωW [] ps y ys c 0)) (proj₂ R₀))
          (λ k → proj₁ (Rk k)) (λ k → subst (Lab _) (sym (ωW [] ps y ys c (suc k))) (proj₂ (Rk k)))
    where
    R₀ = Pre0AS {z = z} {p = p} {σ = σ} h₀ (ŝ-refl₀ ex) (nfω nu c 0)
    Rk = λ k → Pre0AS {z = z} {p = p} {σ = σ} (hk k) (ŝ-reflg ex _ _ _ _ (≅ᴵ-refl _)) (nfω nu c (suc k))
  Pre0AS {a = []} (lĉ () K h₀ hk) ex nu
  Pre0AS {z = z} {p = p} {σ = σ} {a = y ∷ ys} (lĉ c K h₀ hk) ex nu =
    ĉᴸ-mk nu (cofω′ c) K (proj₁ R₀) (subst (Lab _) (sym (ωW [] ps y ys c 0)) (proj₂ R₀))
          (λ k → proj₁ (Rk k)) (λ k → subst (Lab _) (sym (ωW [] ps y ys c (suc k))) (proj₂ (Rk k)))
    where
    R₀ = Pre0AS {z = z} {p = p} {σ = σ} h₀ (ĉ-refl₀ ex) (nfω nu c 0)
    Rk = λ k → Pre0AS {z = z} {p = p} {σ = σ} (hk k) (ĉ-reflg ex _ _) (nfω nu c (suc k))

  Pre0VS {k = zero}    {z = z} {p = p} {σ = σ} at ex nu = Pre0AS {z = z} {p = p} {σ = σ} (atomL at) ex nu
  Pre0VS {k = suc _}   {z = z} {p = p} {σ = σ} h  ex nu = Pre0S₊ {z = z} {p = p} {σ = σ} h ex nu
  Pre0VS {k = lim _ _} {z = z} {p = p} {σ = σ} h  ex nu = Pre0S₊ {z = z} {p = p} {σ = σ} h ex nu

  Pre0S₊ {z = z} {p = p} {a = []} (gz c) ex nu = pop0 {z = z} {p = p} nu
  Pre0S₊ {a = y ∷ ys} (gz c) ex nu = ⊥-elim (cof-ne y ys c)
  Pre0S₊ {a = []} (gs () l) ex nu
  Pre0S₊ {z = z} {p = p} {σ = σ} {a = y ∷ ys} (gs c l) ex nu =
    limᴸ nu cω′ (λ m → proj₁ (Rs m)) (λ m → subst (Lab _) (sym (repW [] ps y ys c m)) (proj₂ (Rs m)))
    where
    cω′ = trans (cofW [] ps y ys) (cong (cofA []) c)
    Rp = Pre0S₊ {z = z} {p = p} {σ = σ} l (s-invˢ ex) (subst NF₁ (repW [] ps y ys c 1) (NF₁-fsn nu cω′ 1))
    Rs = repᴸ (proj₁ Rp) (proj₂ Rp) (λ m → subst NF₁ (repW [] ps y ys c m) (NF₁-fsn nu cω′ m))
  Pre0S₊ {a = []} (gl () h) ex nu
  Pre0S₊ {z = z} {p = p} {σ = σ} {a = y ∷ ys} (gl c h) ex nu =
    limᴸ nu (cofω′ c)
         (λ m → proj₁ (Pre0S₊ {z = z} {p = p} {σ = σ} (h m) (l-invˢ ex m) (nfω nu c m)))
         (λ m → subst (Lab _) (sym (ωW [] ps y ys c m)) (proj₂ (Pre0S₊ {z = z} {p = p} {σ = σ} (h m) (l-invˢ ex m) (nfω nu c m))))
  Pre0S₊ {z = z} {p = p} {σ = σ} (gu {r = zero} l) ex nu =
    Pre0VS {z = z} {p = p} {σ = λ q → σ (suc q)} l (u-reflˢ zero ex) nu
  Pre0S₊ {z = z} {p = p} {σ = σ} (gu {r = self m} l) ex nu =
    Pre0VS {z = z} {p = p} {σ = λ q → σ (lim m q)} l (u-reflˢ (self m) ex) nu
  Pre0S₊ {a = []} (gi () I ej h) ex nu
  Pre0S₊ {z = z} {p = p} {σ = σ} {a = y ∷ ys} (gi {j = zero} {q = q} {f = f} c I ej h) ex nu =
    liLabS {z = z} {p = p} {σ = σ} {q = q} {f = f} (trans c (cong cΩ (kdI I (sym (kd-≅ ej))))) ex nu
           (λ p′ θ x at br nf → Pre0S₊ {z = z} {p = p′} {σ = σ} (h θ x (→Ll (<→◃ q) at)) br nf)
  Pre0S₊ {a = y ∷ ys} (gi {ν = []} {j = suc _} c I ej h) ex nu = ⊥-elim (tf (trans (sym (kdI[] I)) (sym (kd-≅ ej))))
  Pre0S₊ {z = z} {p = p} {σ = σ} {a = y ∷ ys} (gi {ν = v ∷ vs} {j = suc _} {q = q} {f = f} c I ej h) ex nu =
    foldLabS {z = z} {p = p} {σ = σ} {q = q} {f = f} c I ej refl ex nu (λ η x l → h η x (→Ll (<→◃ q) l))
             (λ η x l br nf → Pre0S₊ {z = z} {p = p} {σ = σ} (h η x (→Ll (<→◃ q) l)) br nf)
  Pre0S₊ {a = y ∷ ys} (gi {ν = []} {j = lim _ _} c I ej h) ex nu = ⊥-elim (tf (trans (sym (kdI[] I)) (sym (kd-≅ ej))))
  Pre0S₊ {z = z} {p = p} {σ = σ} {a = y ∷ ys} (gi {ν = v ∷ vs} {j = lim _ _} {q = q} {f = f} c I ej h) ex nu =
    foldLabS {z = z} {p = p} {σ = σ} {q = q} {f = f} c I ej refl ex nu (λ η x l → h η x (→Ll (<→◃ q) l))
             (λ η x l br nf → Pre0S₊ {z = z} {p = p} {σ = σ} (h η x (→Ll (<→◃ q) l)) br nf)
  Pre0S₊ {k = zero} (gŝ () c Iw bw ow h₀ hg) ex nu
  Pre0S₊ {k = suc _} {a = []} (gŝ kk () Iw bw ow h₀ hg) ex nu
  Pre0S₊ {k = suc _} {z = z} {p = p} {σ = σ} {a = y ∷ ys} (gŝ kk c Iw bw ow h₀ hg) ex nu =
    ŝChainS {z = z} {p = p} {σ = σ} c nu Iw bw ow
            (Pre0S₊ {z = z} {p = p} {σ = σ} h₀ (ŝ-refl₀ ex) (nfγ nu c 0))
            (λ m Y hY lY e → Pre0S₊ {z = z} {p = p} {σ = σ} (hg _ Y hY lY (nfγ nu c m) (1<γ ps y ys c m) e)
                                    (ŝ-reflg ex _ _ _ _ (≅ᴵ-refl _)) (nfγ nu c (suc m)))
  Pre0S₊ {k = lim _ _} {a = []} (gŝ kk () Iw bw ow h₀ hg) ex nu
  Pre0S₊ {k = lim _ _} {z = z} {p = p} {σ = σ} {a = y ∷ ys} (gŝ kk c Iw bw ow h₀ hg) ex nu =
    ŝChainS {z = z} {p = p} {σ = σ} c nu Iw bw ow
            (Pre0S₊ {z = z} {p = p} {σ = σ} h₀ (ŝ-refl₀ ex) (nfγ nu c 0))
            (λ m Y hY lY e → Pre0S₊ {z = z} {p = p} {σ = σ} (hg _ Y hY lY (nfγ nu c m) (1<γ ps y ys c m) e)
                                    (ŝ-reflg ex _ _ _ _ (≅ᴵ-refl _)) (nfγ nu c (suc m)))
  Pre0S₊ {a = []} (gĉ () K h₀ hk) ex nu
  Pre0S₊ {z = z} {p = p} {σ = σ} {a = y ∷ ys} (gĉ c K h₀ hk) ex nu =
    ĉᴸ-mk nu (cofω′ c) K (proj₁ R₀) (subst (Lab _) (sym (ωW [] ps y ys c 0)) (proj₂ R₀))
          (λ k → proj₁ (Rk k)) (λ k → subst (Lab _) (sym (ωW [] ps y ys c (suc k))) (proj₂ (Rk k)))
    where
    R₀ = Pre0S₊ {z = z} {p = p} {σ = σ} h₀ (ĉ-refl₀ ex) (nfω nu c 0)
    Rk = λ k → Pre0S₊ {z = z} {p = p} {σ = σ} (hk k) (ĉ-reflg ex _ _) (nfω nu c (suc k))
```

**读法.** 停机一次通过; 互递归 `Pre0S₊ → {pop0, liLabS, foldLabS → PreS₊, ŝChainS}` 全在尾巴推导上.

## §6 好栈: 空栈、$\hat\Omega$ 帧、可数指数帧

`Goodˢ S ps`: 三个假设的记录. `Good∅`: 空栈的值 $\Omega_i$ 带标签 $\Omega_w$ (`LabL-Ω`, 即 GoodLBase `PsiL₊` 的 `gz` 情形), 目标 $0$ 时是 $1=\psi_0(0)$. `GoodΩ`: OmegaKBase `popLK`/`pop0K` 的 "一步" 版. 目标 $w\ne0$: 闭包的 `gŝ` 行 (地板 $w$, 界 $i+1$, 出现 `oh`), 第 0 点与分支由 `PreW` 在尾巴 $\Omega_1$、$\Omega_{\mathtt{lvl}\,Y}$ 处给出, 记号 `H1W` ($\psi_w(ps+\Omega_\Omega)[\theta]=\psi_w(ps+\Omega_\theta)$). 目标 $0$: 链证书, 标签序列 `γs j = γW ps [Ω_Ω] [] (suc j)` (字面 cons, `one⊑lab` 的 `[]<` 直接可用), 点由 `Pre0` 给出, 记号 `gtW`.

```agda
record Goodˢ (S : Stk) (ps : T) : Set where
  constructor good
  field
    hW : HypW S ps
    h0 : Hyp0 S ps
    hR : S ≈ˢ S
open Goodˢ public

Good∅ : Goodˢ ∅ˢ []
Good∅ = good (λ { z p (Y , hY , lY , nY) ei ki → toL₊ ki (LabL-Ω Y hY lY nY ei) })
             (λ z p nf → gs gz , l1 refl (s≅ z≅) (l0 refl z≅))
             ∅-≈

GoodΩ : ∀ {S : Stk} {ps} → Goodˢ S ps → Goodˢ (S ▹Ω̂) (ps ++ ΩΩ ∷ [])
GoodΩ {S = S} {ps} G = good hW′ h0′ (▹Ω̂-≈ (hR G))
  where
  open PreW S ps (hW G)
  open Pre0 S ps (hW G) (h0 G) (hR G)
  fsTe : ∀ x xs θ → fsT (πw (x ∷ xs) ps (ΩΩ ∷ [])) θ ≡ πw (x ∷ xs) ps (Ωt θ)
  fsTe x xs θ = H1W x xs ps ΩΩ [] refl θ
  hW′ : HypW (S ▹Ω̂) (ps ++ ΩΩ ∷ [])
  hW′ {w = []} z p Iw ei ki = ⊥-elim (ne-w Iw ei ki refl)
  hW′ {i = i} {w = x ∷ xs} z p Iw ei ki =
    gŝ ki (trans (cofW (x ∷ xs) ps ΩΩ []) (H1-pen x xs)) Iw (⊑ᴵ-≅ʳ ⊑ᴵ-refl (s≅ ei))
       (λ θ → subst (Occ (x ∷ xs)) (sym (fsTe x xs θ)) oh)
       (subst (LabL₊ _ Ll _) (sym (fsTe x xs (natT 1)))
              (PreVS {z = z<suc z p} {p = zero} {σ = σ1 (z<suc z p)} Iw ei ki (LabL-Ω one⁰ (hs hz) lab1 nf1 (≅ᴵ-refl _))))
       (λ θ Y hY lY nθ lt e → subst (LabL₊ _ Ll _) (sym (fsTe x xs θ))
              (PreVS {z = lim 0 (z<suc z p)} {p = lim 0 zero} {σ = λ q → lim 1 q} Iw ei ki (LabL-Ω Y hY lY nθ (≅ᴵ-refl _))))
  t : T
  t = πw [] ps (ΩΩ ∷ [])
  γs : ℕ → T
  γs j = γW ps (ΩΩ ∷ []) [] (suc j)
  fsγ : ∀ j → fsn t j ≡ γs j
  fsγ j = gtW [] ps ΩΩ [] [] refl refl j
  cofE : cof t ≡ cω
  cofE = cofW [] ps ΩΩ []
  h0′ : Hyp0 (S ▹Ω̂) (ps ++ ΩΩ ∷ [])
  h0′ z p nf =
    ĉᴸ-mk nf cofE K (proj₁ R₀) (subst (Lab _) (sym (fsγ 0)) (proj₂ R₀))
          (λ k → CCᴸ.Gg K k (Ptᴸ.x (ptK K k)) (Ptᴸ.hx (ptK K k)) (Ptᴸ.lx (ptK K k)) (Ptᴸ.dx (ptK K k)))
          (λ k → subst (Lab _) (sym (fsγ (suc k)))
                       (CCᴸ.lE K k (Ptᴸ.x (ptK K k)) (Ptᴸ.hx (ptK K k)) (Ptᴸ.lx (ptK K k)) (Ptᴸ.dx (ptK K k))))
    where
    o = z<suc z p
    nfγs : ∀ j → NF₁ (γs j)
    nfγs j = subst NF₁ (fsγ j) (NF₁-fsn nf cofE j)
    R₀ = Pre0VS {z = o} {p = zero} {σ = σ1 o} (LabL-Ω one⁰ (hs hz) lab1 nf1 (≅ᴵ-refl _)) (Ωˢ-refl (suc zero)) (nfγs 0)
    Rg : ∀ j Y (hY : HS Y) → Lab Y (γs j) → (e : suc zero ⊑ᴵ toLevel Y hY) →
         Σ (Goodᴸ (toZ (ψˢ S {ℓ = Mlev (suc zero) (toLevel Y hY) e} (lim 0 o) (lim 0 zero) (λ q → lim 1 q) (Ωˢ (toLevel Y hY))))) λ G →
           Lab (forceᴸ _ G) (γs (suc j))
    Rg j Y hY lY e = Pre0VS {z = lim 0 o} {p = lim 0 zero} {σ = λ q → lim 1 q}
                            (LabL-Ω Y hY lY (nfγs j) (≅ᴵ-refl _)) (Ωˢ-refl _) (nfγs (suc j))
    K = ccᴸ γs (proj₁ R₀) (proj₂ R₀) (one⊑lab _ (proj₂ R₀) (nfγs 0) []<)
            (λ j Y hY lY e → proj₁ (Rg j Y hY lY e)) (λ j Y hY lY e → proj₂ (Rg j Y hY lY e))
            (λ j Y hY lY e → one⊑lab _ (proj₂ (Rg j Y hY lY e)) (nfγs (suc j)) []<)
```

**读法.** OmegaKBase 的 `popLK (suc m)`/`pop0K (suc m)` 递归调用 `PreVK m`/`Pre0VK m`, 为的是标 $m+1$ 帧的树; 这里剩余栈的标签是 `Goodˢ S ps` 的字段, 所以 `GoodΩ` 非递归, 帧数归纳变成了好栈的逐层构造.

**可数指数帧.** `GoodE` 对指数 $X$ 的 `Lab0ᴸ` 推导 (第 0 层的结构标签) 递归, 结论是新栈的三个字段. 记号: $\psi_w(ps+\psi_\Omega(\eta))$ 的末项在 $\eta$ 为后继或极限时共尾度 $\omega$ (`cofA Ωᵗ c1`、`cofA Ωᵗ cω` 都是 `cω`), $[n]$ 是 $\psi_\Omega(\eta-1)\cdot n$ (`fs-rep Ωᵗ`) 或 $\psi_\Omega(\eta[n])$ (`fs-ω Ωᵗ`), 再经 `ωW` 带上前缀. 情形:

- `lz` ($\eta=0$): $\psi_\Omega(0)=\Omega_\Omega$, 就是 `GoodΩ` (`S ▹ω zero` 与 `S ▹Ω̂` 定义性相同).
- `ls`: `repGood` 说 `rep S Y m` 是前缀 `ps ++ replicate m ψ_Ω(η−1)` 的好栈 (对 $m$ 归纳: $m=0$ 经 `++-identityʳ`; $m+1$ 是 `GoodE` 作用于同一个前驱推导 `l`, 前缀经 `snoc` 改写); 然后 `gl`/`limᴸ`.
- `ll`: 逐项递归.
- `lŝ₀`/`lĉ`: 指数是第 0 层的待计值链, 计值树是同一条链上的 `ĉᴸ`, 输出换成新栈的值; 链证书 `K` 原样交给 `gĉ`/`ĉᴸ-mk`. 这正是 "指数为极限的帧弹出为各项帧的极限" 在待计值链上的形式.

```agda
rep-snoc : ∀ m (x : PT) → replicate m x ++ (x ∷ []) ≡ x ∷ replicate m x
rep-snoc zero    x = refl
rep-snoc (suc m) x = cong (x ∷_) (rep-snoc m x)

snoc : ∀ ps m (x : PT) → (ps ++ replicate m x) ++ (x ∷ []) ≡ ps ++ replicate (suc m) x
snoc ps m x = trans (++-assoc ps (replicate m x) (x ∷ [])) (cong (ps ++_) (rep-snoc m x))

GoodE   : ∀ {S : Stk} {ps} → Goodˢ S ps → ∀ {X : Ordˢ zero} {η} → Lab0ᴸ X η → X ≅ˢ X → Goodˢ (S ▹ω X) (ps ++ ψᵗ Ωᵗ η ∷ [])
repGood : ∀ {S : Stk} {ps} → Goodˢ S ps → ∀ {Y : Ordˢ zero} {θ} → Lab0ᴸ Y θ → Y ≅ˢ Y → ∀ m →
          Goodˢ (rep S Y m) (ps ++ replicate m (ψᵗ Ωᵗ θ))

repGood {S = S} {ps} G l ey zero    = subst (Goodˢ S) (sym (++-identityʳ ps)) G
repGood {S = S} {ps} G {Y = Y} {θ = θ} l ey (suc m) =
  subst (Goodˢ (rep S Y (suc m))) (snoc ps m (ψᵗ Ωᵗ θ)) (GoodE (repGood G l ey m) l ey)

GoodE G {η = []} (lz c) ex = GoodΩ G
GoodE G {η = y ∷ ys} (lz c) ex = ⊥-elim (cof-ne y ys c)
GoodE G {η = []} (ls () l) ex
GoodE {S = S} {ps} G {X = Ord₊ˢ.suc Y} {η = y ∷ ys} (ls c l) ex = good hW′ h0′ (▹ω-≈ (hR G) ex)
  where
  x = ψᵗ Ωᵗ (pred (y ∷ ys))
  RG : ∀ m → Goodˢ (rep S Y m) (ps ++ replicate m x)
  RG = repGood G l (s-invˢ ex)
  cE : ∀ w → cof (πw w ps (ψᵗ Ωᵗ (y ∷ ys) ∷ [])) ≡ cω
  cE w = trans (cofW w ps (ψᵗ Ωᵗ (y ∷ ys)) []) (cong (cofA w) (cong (cofA Ωᵗ) c))
  fsE : ∀ w m → fsn (πw w ps (ψᵗ Ωᵗ (y ∷ ys) ∷ [])) m ≡ πw w ps (replicate m x)
  fsE w m = trans (ωW w ps (ψᵗ Ωᵗ (y ∷ ys)) [] (cong (cofA Ωᵗ) c) m)
                  (cong (πw w ps) (fs-rep Ωᵗ y ys c m))
  hW′ : HypW (S ▹ω Ord₊ˢ.suc Y) (ps ++ ψᵗ Ωᵗ (y ∷ ys) ∷ [])
  hW′ {w = w} z p Iw ei ki = gl (cE w) (λ m → subst (LabL₊ _ Ll _) (sym (fsE w m)) (hW (RG m) z p Iw ei ki))
  h0′ : Hyp0 (S ▹ω Ord₊ˢ.suc Y) (ps ++ ψᵗ Ωᵗ (y ∷ ys) ∷ [])
  h0′ z p nf = limᴸ nf (cE []) (λ m → proj₁ (Rm m)) (λ m → subst (Lab _) (sym (fsE [] m)) (proj₂ (Rm m)))
    where Rm = λ m → h0 (RG m) z p (subst NF₁ (fsE [] m) (NF₁-fsn nf (cE []) m))
GoodE G {η = []} (ll () h) ex
GoodE {S = S} {ps} G {X = Ord₊ˢ.lim F} {η = y ∷ ys} (ll c h) ex = good hW′ h0′ (▹ω-≈ (hR G) ex)
  where
  GE : ∀ n → Goodˢ (S ▹ω F n) (ps ++ ψᵗ Ωᵗ (fsn (y ∷ ys) n) ∷ [])
  GE n = GoodE G (h n) (l-invˢ ex n)
  cE : ∀ w → cof (πw w ps (ψᵗ Ωᵗ (y ∷ ys) ∷ [])) ≡ cω
  cE w = trans (cofW w ps (ψᵗ Ωᵗ (y ∷ ys)) []) (cong (cofA w) (cong (cofA Ωᵗ) c))
  fsE : ∀ w n → fsn (πw w ps (ψᵗ Ωᵗ (y ∷ ys) ∷ [])) n ≡ πw w ps (ψᵗ Ωᵗ (fsn (y ∷ ys) n) ∷ [])
  fsE w n = trans (ωW w ps (ψᵗ Ωᵗ (y ∷ ys)) [] (cong (cofA Ωᵗ) c) n) (cong (πw w ps) (fs-ω Ωᵗ y ys c n))
  hW′ : HypW (S ▹ω Ord₊ˢ.lim F) (ps ++ ψᵗ Ωᵗ (y ∷ ys) ∷ [])
  hW′ {w = w} z p Iw ei ki = gl (cE w) (λ n → subst (LabL₊ _ Ll _) (sym (fsE w n)) (hW (GE n) z p Iw ei ki))
  h0′ : Hyp0 (S ▹ω Ord₊ˢ.lim F) (ps ++ ψᵗ Ωᵗ (y ∷ ys) ∷ [])
  h0′ z p nf = limᴸ nf (cE []) (λ n → proj₁ (Rm n)) (λ n → subst (Lab _) (sym (fsE [] n)) (proj₂ (Rm n)))
    where Rm = λ n → h0 (GE n) z p (subst NF₁ (fsE [] n) (NF₁-fsn nf (cE []) n))
GoodE G {η = []} (lŝ₀ () K h₀ hk) ex
GoodE {S = S} {ps} G {X = Ord₊ˢ.ŝ c′ t₀ g} {η = y ∷ ys} (lŝ₀ c K h₀ hk) ex = good hW′ h0′ (▹ω-≈ (hR G) ex)
  where
  GE₀ = GoodE G h₀ (ŝ-refl₀ ex)
  GEk = λ k → GoodE G (hk k) (ŝ-reflg ex _ _ _ _ (≅ᴵ-refl _))
  cE : ∀ w → cof (πw w ps (ψᵗ Ωᵗ (y ∷ ys) ∷ [])) ≡ cω
  cE w = trans (cofW w ps (ψᵗ Ωᵗ (y ∷ ys)) []) (cong (cofA w) (cong (cofA Ωᵗ) c))
  fsE : ∀ w n → fsn (πw w ps (ψᵗ Ωᵗ (y ∷ ys) ∷ [])) n ≡ πw w ps (ψᵗ Ωᵗ (fsn (y ∷ ys) n) ∷ [])
  fsE w n = trans (ωW w ps (ψᵗ Ωᵗ (y ∷ ys)) [] (cong (cofA Ωᵗ) c) n) (cong (πw w ps) (fs-ω Ωᵗ y ys c n))
  hW′ : HypW (S ▹ω Ord₊ˢ.ŝ c′ t₀ g) (ps ++ ψᵗ Ωᵗ (y ∷ ys) ∷ [])
  hW′ {w = w} z p Iw ei ki =
    gĉ (cE w) K (subst (LabL₊ _ Ll _) (sym (fsE w 0)) (hW GE₀ z p Iw ei ki))
       (λ k → subst (LabL₊ _ Ll _) (sym (fsE w (suc k))) (hW (GEk k) z p Iw ei ki))
  h0′ : Hyp0 (S ▹ω Ord₊ˢ.ŝ c′ t₀ g) (ps ++ ψᵗ Ωᵗ (y ∷ ys) ∷ [])
  h0′ z p nf =
    ĉᴸ-mk nf (cE []) K (proj₁ R₀) (subst (Lab _) (sym (fsE [] 0)) (proj₂ R₀))
          (λ k → proj₁ (Rk k)) (λ k → subst (Lab _) (sym (fsE [] (suc k))) (proj₂ (Rk k)))
    where
    R₀ = h0 GE₀ z p (subst NF₁ (fsE [] 0) (NF₁-fsn nf (cE []) 0))
    Rk = λ k → h0 (GEk k) z p (subst NF₁ (fsE [] (suc k)) (NF₁-fsn nf (cE []) (suc k)))
GoodE G {η = []} (lĉ () K h₀ hk) ex
GoodE {S = S} {ps} G {X = Ord₊ˢ.ĉᴸ c′ t₀ g o₀ o} {η = y ∷ ys} (lĉ c K h₀ hk) ex = good hW′ h0′ (▹ω-≈ (hR G) ex)
  where
  GE₀ = GoodE G h₀ (ĉ-refl₀ ex)
  GEk = λ k → GoodE G (hk k) (ĉ-reflg ex _ _)
  cE : ∀ w → cof (πw w ps (ψᵗ Ωᵗ (y ∷ ys) ∷ [])) ≡ cω
  cE w = trans (cofW w ps (ψᵗ Ωᵗ (y ∷ ys)) []) (cong (cofA w) (cong (cofA Ωᵗ) c))
  fsE : ∀ w n → fsn (πw w ps (ψᵗ Ωᵗ (y ∷ ys) ∷ [])) n ≡ πw w ps (ψᵗ Ωᵗ (fsn (y ∷ ys) n) ∷ [])
  fsE w n = trans (ωW w ps (ψᵗ Ωᵗ (y ∷ ys)) [] (cong (cofA Ωᵗ) c) n) (cong (πw w ps) (fs-ω Ωᵗ y ys c n))
  hW′ : HypW (S ▹ω Ord₊ˢ.ĉᴸ c′ t₀ g o₀ o) (ps ++ ψᵗ Ωᵗ (y ∷ ys) ∷ [])
  hW′ {w = w} z p Iw ei ki =
    gĉ (cE w) K (subst (LabL₊ _ Ll _) (sym (fsE w 0)) (hW GE₀ z p Iw ei ki))
       (λ k → subst (LabL₊ _ Ll _) (sym (fsE w (suc k))) (hW (GEk k) z p Iw ei ki))
  h0′ : Hyp0 (S ▹ω Ord₊ˢ.ĉᴸ c′ t₀ g o₀ o) (ps ++ ψᵗ Ωᵗ (y ∷ ys) ∷ [])
  h0′ z p nf =
    ĉᴸ-mk nf (cE []) K (proj₁ R₀) (subst (Lab _) (sym (fsE [] 0)) (proj₂ R₀))
          (λ k → proj₁ (Rk k)) (λ k → subst (Lab _) (sym (fsE [] (suc k))) (proj₂ (Rk k)))
    where
    R₀ = h0 GE₀ z p (subst NF₁ (fsE [] 0) (NF₁-fsn nf (cE []) 0))
    Rk = λ k → h0 (GEk k) z p (subst NF₁ (fsE [] (suc k)) (NF₁-fsn nf (cE []) (suc k)))
```

**读法.** 停机一次通过: `GoodE (ls c l) → repGood … l … m → GoodE … l` 中推导严格下降 (`ls c l` 到 `l`), `repGood (suc m) → repGood m` 中重数下降而推导不变. 这是折叠 `ψᵉ`/`rep` 的度量 (指数, 重数) 在证明里的影子: 指数的标签推导代替指数树. 唯一跨栈的调用 `GoodE (repGood G l ey m) l ey` 写在顶层子句里, 没有 `where` 链体的问题.

## §7 对比表

| | OmegaKBase ($\Omega_\Omega\cdot k$) | 本文 |
|---|---|---|
| 栈 | `Vec (Frame ℓ) (suc n)` + `AΩ P` | `Stk` (续延, 对目标与环境层号多态), 无下标 |
| 帧 | `fΩ̂` | `▹Ω̂`, `▹ω X` (第 0 层指数), `▹Ω̂²` (指数 $\Omega_\Omega$) |
| 停机度量 | (帧数, 尾巴) | 尾巴折叠: 尾巴; 指数折叠: (指数, 重数) |
| 弹 $\hat\Omega$ | `pop-eq` 改写 `rebase` | 定义性 (`▹Ω̂` 直接是闭包) |
| 记号前缀 | `ΠΩ (suc n) b` (字面 cons) | 任意 `ps ++ b` (`onCons` 分情形) |
| 带前缀引理 | 对 $n$ 归纳的 `PreK₊`/`Pre0K₊` | 参数化模块 `PreW`/`Pre0`, 弹栈 = 假设 |
| 帧数归纳 | `popLK`/`pop0K` 递归到 $n-1$ 帧 | `Goodˢ` 的逐层构造: `Good∅`, `GoodΩ`, `GoodE` |
| 指数 $\omega^{\eta+1}$ | (无) | `repGood`: $m$ 个 $\omega^\eta$ 帧, 对 $m$ 归纳 |
| `Goodᴸ`/`gc`/`forceᴸ`/`limᴸ`/`ĉᴸ-mk`/`fs-mono₁`/`LabL` | 原样 | 原样 |
| `domᴸ` | 原样 (`OccΠ n`) | `domS` (任意前缀, `OccΣ ps`), 证明同 |
| `1<ctx` | 原样 | `1<γ` (`fsT-ne`, `++-ne`) |

## §8 结论与边界

**定理 (对一切栈与推导):**

1. 记号: `onCons`, `cofΣ`/`predΣ`/`fsnΣ`/`fsTΣ`/`OccΣ`, `cofW`/`repW`/`ωW`/`γW-eq`/`gtW`/`penW`/`H1W`, `1<π`, `1<ψ`, `++-ne`, `fsT-ne`, `1<γ`.
2. 折叠: `ψˢ`, `∅ˢ`, `▹Ω̂`, **`ψᵉ`/`rep`/`▹ω`** (结构递归, 无下标), `▹Ω̂²`.
3. 互模拟: `ψˢ-≅` (+ `liS`), `∅-≈`, `▹Ω̂-≈`, `ψᵉ0-≅`/`rep-≈`, `▹ω-≈`, `chainS-≅`, `fold1S`, `pen1S`.
4. 一般栈: `PreW.PreS₊` (目标 $w\ne0$), `Pre0.Pre0S₊` (目标 $0$, 证书与标签), `domS`.
5. 好栈: `Good∅`, `GoodΩ`, **`GoodE`**, `repGood`, `snoc`.

**边界.**

- 入栈的指数只在第 0 层 (`Ordˢ zero`, 带 `Lab0ᴸ` 推导与自互模拟). `ψᵉ` 接受任意层的指数作栈顶 (`limᵢ`/`up`/`ŝ` 子句), 但第 $\ge1$ 层的后继是占位值 $\Omega_i$, 本文没有它的标签理论; 第 $\ge1$ 层指数的带前缀引理 (以指数为 "尾巴" 的 `PreS₊`/`Pre0S₊`) 未写.
- `Goodˢ` 的 `HypW` 对一切目标与环境层号量化 (栈的多态性); 证书只在带标签的点处 (`Goodᴸ`), 与 GoodLBase 相同.
- 不改 `src/`、`archive/` 与已有的 Align 文件, README 未改.
