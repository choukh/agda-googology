# 降维打击的检验 (不含记号的部分)

> 底座 [InaccStrikeBase](InaccStrikeBase.lagda.md), 判决 [InaccStrikeOracle](InaccStrikeOracle.lagda.md); 记号只在 [InaccStrikeCommute](InaccStrikeCommute.lagda.md)、[InaccStrikeNat](InaccStrikeNat.lagda.md)、[InaccStrikeAccept](InaccStrikeAccept.lagda.md). 本文与前两个文件的导入链不含 `OCF.Align.EBO`.
>
> **判决: PLATFORM, 而且只在标签路线上. 不是 STRIKE, 没有被 REFUTED.** 证书路线上是 NO GAIN, 目前落后于 Uniform3.
>
> **已编译的事实.**
>
> 1. **`Commute` 成立 (条件式).** 一个证明覆盖全部阶段与全部深度: 判决在下标对上正确 (`GV`), 项类封闭 (`P-fs`, `P-pr`), 外延性 ⟹ `LabN (dz (S t)) t`. 证明中没有地板、深度、阶段, 也不用单调性. 所以 "逐项一致" 已归结为判决的正确性 + 项的封闭性.
> 2. **前提可满足, 但只到有限下标.** `nat-label`: 判决 `ver`, 下标为自然数, 任意可数项 (不要求标准形), 只以 `Funext` 为参数.
> 3. **`ver` 的树确实偏离 EBO.** 标准形 `ψ₀(ψ_{Ω₂}(Ω_{Ω₁+1}))` 在路径 `[1,0,0,1,0,0,0]` 处不一致 (`ver-dev`); 原因是 `ver` 答 `Ω₁` 不低于 `Ω₂` (`ver-rise-Ω`). 上一轮宽度 1 查不到是因为偏离在第 1 号分支.
> 4. **`Agree` 的原始形式不够.** 常值的搬运不改变判决标签与路径, 树却错了 (`b-bad`).
> 5. **选项 (a) 的第一个障碍在 ψ₀(Ω_Ω·2), 早于 (Ω_Ω)².** `T₂-cert→⊥`: 对**任何**判决, `ψ₀(Ω_Ω·2)` 的证书不能与 "`G` 含 `ω+2`、`0`、穿透后的 `suc ω⁺T`" 并存. `ω⁺T = lim[1,2,…]` 单调, 值为 ω, 对 ω+1 没有可靠判决 (`no-sound`). 它也是 `1+ω` 的形状 (`no-sound-1+ω`), 所以 `G` 不能对 + 封闭: "降序和" 这条标准形条件是树侧推出来的. 这只否定含这类树的 `G`, 不否定一切 `G`.
> 6. **`G` 的三个性质.** `ω` 与 `ω⁺` 互不可比 (`ω≇ω⁺`, `ω⊀ω⁺`, `ω⁺⊀ω`). 生成类的 `Gen`/`Run` 互递归不严格正 (编译器拒绝, 试验未保留). 对 `n` 分层的 `Gs` 使 `Close` 成为定义 (`Tower.close`).
> 7. **选项 (b): 没有一般的否定, 唯一的构造尝试失败.** 候选 `D★` (由树读 `nrm`、`toT`, 采样 `same★`) 修掉了第 3 点的偏离, 通过 `tΩ2`、`tP2 = ψ₀(ψ_Ω(ψ_Ω(Ω_Ω)))`、`EBOψ 3` 的 `diff`, 但在同一标准形层号上判 `≺` (`★-wrong-OO`, `★-wrong-Ω₂`). 三版修补都只是把错误推后. `D★-pad`: 它在单调的填充树上也是错的, 所以模不是层号自身的性质, 只可能是某个规整类的性质. 范数能否从树读出: 这三版没有给出肯定的证据, 否定也只针对这个候选.
>
> **第一个具体障碍.** 没有任何总判决对奇异 Ω 下标正确. 具体地, 在 `limᴼ k g` 目标上判 `j ≺ g x` 时, `x` 的读取与层号相等的判定都没有可靠的方法: 第 `k` 层的树可以在有限采样下模仿 `j` (`★-wrong-OO`). 即使有了判决, 证 `GV` 还需要项侧的封闭性与 Bachmann 性质 (调研说 koteitan 的 Lean 有 `OTFS_thm` 与 `bachmann`, 我没有构建或核对, 其基本列是否与 `EBO.lagda.md` 逐条相同也未核对). 下一步最小的决定性检验: 先把 `N` 从自然数扩到可数标准形, 看 `lim` 目标上的范数模能否证出; 这一段不碰奇异下标.
>
> **以下是判断, 不是定理.**
>
> - **对角论证没有入口.** 目标类是固定的、在项上可判定的集合, 没有自由度可以对角化. 字面碰撞 (两个 NF 层号相同而判决应不同) 与 Bachmann 性质矛盾, 所以不指望.
> - **证据消费的折叠不成立.** `pen` 的输出是对**全部** `y` 的函数, 证据只对好的 `y` 有; 好不可判定 (`¬SoundAll`, WLPO). 所以折叠必须是总函数 + 外部证书, 选项 (a) 不能绕开总判决, 只是把它的正确性限制到 `G` 上. 带证据的折叠若不走这条路, 就要延迟分支 (帧/替身), 那就回到 `Goodᴸ`/`forceᴸ`.
> - **地板与塔.** 地板对应 "目标与节点在公共 WF 界下的路径": `<-dec` 比较的是路径数据, 这正是它不需要搜索、不碰 WLPO 的原因. 去掉它, 比较就要搜索, 搜索要模. 塔则在证书里以分层的 `G` 出现: `rc` 要求同一层封闭, 而 `Gs` 每折叠一步升一层; 另外的分层方式我没有排除.
> - **与 Uniform3 的比较 (新基线).** Uniform3 有无条件 `TΩ2-label`, 其 `<ᴵ-dec` 是定理, 代价是 `Goodᴸ`、`Hn`、地板. `Lv` 上标签的全部结构部分是 335 行代码 (Base 114 + Commute 221) 且对阶段一致, Uniform3 系列 9 个文件共 3774 行代码 (口径不完全相同: 后者含证书与判决的定理), 但这里的比较是假设. 所以省下的是定义机器与标签的簿记, 没省的是比较的真实性. **公平检验的回答:** 不含记号的 `Lv` 证据**没有**到达 (Ω_Ω)², 连 ψ₀(Ω_Ω·2) 也没有. 深度 2 在定义与 `Commute` 里不是一个概念, 没有新情形 (`tP2` 只是有限检验); 但它的 `N` 与 (Ω_Ω)² 同样要包含可数 NF 下标, 所以前提并不因此变小.
> - **`UniformPending` 的 k = 3 障碍.** 它是弹栈支配的问题, 只在证书里出现. `Commute` 不用支配, 该障碍变成 `GV` 的一个实例 (`ν ≥ u` 时答 `rise`); 证书路线没走到那里.
>
> **I 在 Λ 之下的贡献: 没有.** `S`、`ψS`、`Commute` 的定义与证明都不用 `OrdI`; `T0` 只是 `Tr.⟦_⟧` 的方便. 把 I 当公共环境的打法被 `noBT` 与 `Trich₂→WLPO` 挡住.
>
> **来源.** 树侧推出: `limᴼ`, 折叠的 `Verdict` 形状 (`Pre` 路径来自类型), `G` 的非规范性, 降序和的必要性. 读记号: `S` 的形状, `GV` 的 `cmpᵀ` 规格, `P` 的封闭性假设. 启发 (读范数与 `G` 的直觉): `nrm`, `toT`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.InaccStrike where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; cong)

open import OCF.BTBO using (injᵃ; injᵇ; injᶜ)
open import OCF.Align.InaccTreeBase
open import OCF.Align.InaccTree
```

## §1 编译的否定 1: 重排的 ω 没有任何可靠判决

`ω⁺T = lim [1,2,3,…]` 是单调的好树, 值就是 ω. `Sound` 是结构的, 所以它对目标 ω+1 既不 `≺` 也不 `≻` 也不 `≅`: **对任何判决**, `D (toLv ω⁺T) (suc ω)` 都不 `Sound`. 这是 `noBT` 的形式, 这里说的是它的后果: 证书 `Run` 里的好输入类 `G` 不能含这棵树.

```agda
ωL : Lv
ωL = lim natL

i₀ : Lv
i₀ = toLv {zero} (suc ωT)

isNatT : ∀ n → IsNat (toLv {zero} (natT n))
isNatT n = subst IsNat (sym (toLv-nat n)) (natIs n)

-- 一般形: 全由有限数组成且首项非零的 ℕ-极限, 对 ω+1 没有可靠判决
no-sound-gen : (D : Oracle) (f : ℕ → Lv) → (∀ n → IsNat (f n)) → (∀ {a} → f 0 ≅ a → a ≡ zero → ⊥) →
               Sound (D (lim f) i₀) → ⊥
no-sound-gen D f nat f0 s with D (lim f) i₀ | s
... | pen (inj₁ _) b | l≅ h = f0 (h 0) refl
... | pen (inj₂ (m , r)) b | e = lim≇nat (atNat (isNatT m) r) e
... | rise | inj₁ (via (n , r) e) = suc≇ (atNat (nat n) r) e where
  suc≇ : ∀ {g b} → IsNat b → ¬ (suc (lim g) ≅ b)
  suc≇ nz ()
  suc≇ (ns i) (s≅ e′) = lim≇nat i e′
... | rise | inj₂ ()

no-sound : (D : Oracle) → Sound (D (toLv ω⁺T) i₀) → ⊥
no-sound D = no-sound-gen D _ (λ n → isNatT (suc n)) (λ { (s≅ _) () })

-- 同一棵树的另一个来源: 1 + ω. 所以 `G` 不能对 + 封闭, 必须有 "降序和" 的条件
oneω : Ordᴸ zero
oneω = _+_ {zero} (suc zero) ωT

natSum : ∀ n → IsNat (toLv (_+_ {zero} (suc zero) (natT n)))
natSum zero    = ns nz
natSum (suc n) = ns (natSum n)

no-sound-1+ω : (D : Oracle) → Sound (D (toLv oneω) i₀) → ⊥
no-sound-1+ω D = no-sound-gen D _ natSum (λ { (s≅ _) () })
```

## §2 编译的否定 2: `ψ₀(Ω_Ω·2)` 的证书要求上述判决

`Cert.Run D G 0 L₁ (Ω̂ + Ω̂)` 就是 "`ψ₀(Ω_Ω·2)` 的所有判决为真". 走它: 目标 0 的链读 `Ω̂ + Ω(x)`, `x = ω+2` 时 `Ω(x)` 的节点层是 `ω+1`, 目标变成 `ω+1`; 分支 `x′ = 0` 读 `Ω̂`; 目标 `ω+1` 读 `Ω̂` 的节点 (层 0): 穿透, 分支 `y` 读 `Ω(toLv y)`; `y` 是 `suc ω⁺T` 时比较 `ω⁺` 与 `ω+1`. **这条路径上只用了 `Run` 的类型和折叠的定义, 没有记号, 也不依赖 `D`.** 结论: `G` 若含 `ω+2`、`0`、`suc ω⁺T` 的 (穿透后的) 输入, 证书不存在.

```agda
module Forced (D : Oracle) (G : ∀ {k} → Ordᴸ k → Set) where
  open Cert D G
  open Terms D using (Ω̂)

  x₂ : Ordᴸ zero
  x₂ = suc (suc ωT)

  -- 目标 0 上没有穿透: 判决 pen 的路径落在空类型里
  rc-only : ∀ {k r f} → Run zero k (limᵢ r f) →
            ∀ x → G x → Run (at k r) k (f (intoL k r x))
  rc-only (rp {r′ = ()} e s h)
  rc-only (rc e s g₀ h₁ h₂ h₃) = h₁

  rise₀ : ∀ {k r f} → Run zero k (limᵢ r f) →
          ∀ x → G x → Run zero k (f (intoL k r x))
  rise₀ (rp {r′ = ()} e s h)
  rise₀ (rc e s g₀ h₁ h₂ h₃) = h₃

  -- 目标 i₀ 读层 0 的节点: 只能穿透 (rise 要 i₀ ≼ 0)
  pen-only : ∀ {k r f} → at k r ≡ zero → Run i₀ k (limᵢ r f) →
             Σ (Pre i₀) λ r′ → Σ (Ordᴸ (at i₀ r′) → Ordᴸ (at k r)) λ b →
             (∀ y → G y → Run i₀ k (f (intoL k r (b y))))
  pen-only z (rp {r′ = r′} {b = b} e s h) = r′ , b , h
  pen-only {k} {r} z (rc e s g₀ h₁ h₂ h₃) = ⊥-elim (bad (at k r) z s′) where
    s′ = s′′
      where s′′ = subst (λ V → Sound V) e s
    bad : ∀ ℓ → ℓ ≡ zero → (i₀ ≺ ℓ ⊎ i₀ ≅ ℓ) → ⊥
    bad _ refl (inj₁ (via () _))
    bad _ refl (inj₂ ())

  -- 目标 i₀ 读任何后继层的 Ω: 判决必须 Sound
  sound-at : ∀ {k r f} → Run i₀ k (limᵢ r f) → Sound (D (at k r) i₀)
  sound-at (rp e s h)            = s
  sound-at (rc e s g₀ h₁ h₂ h₃) = s
```

**定理.** 对任何判决: `ψ₀(Ω_Ω·2)` 的证书 + `G` 含这三个输入 ⟹ 矛盾. 这是选项 (a) 的第一个障碍, 落在 (Ω_Ω)² 之前. 它不否定一切 `G`, 只否定含非标准形树的 `G`: 好输入类必须把 `ω⁺T` 与 `1+ω` 排除掉, 也就是必须知道标准形. 单调性 (`Goodᶻ`) 不够.

```agda
  T₂-cert→⊥ : Run zero L₁ (Ω̂ + Ω̂) → G x₂ → G {i₀} zero →
              (∀ (r′ : Pre i₀) (b : Ordᴸ (at i₀ r′) → Ordᴸ zero) → Σ (Ordᴸ (at i₀ r′)) λ y → (b y ≡ suc ω⁺T) × G y) → ⊥
  T₂-cert→⊥ run g₂ g₀ H with pen-only {L₁} {inj₁ (inj₁ tt)} refl (rc-only (rise₀ run x₂ g₂) zero g₀)
  ... | r′ , b , h with H r′ b
  ...   | y , e , gy = no-sound D (sound-at (unup (subst (λ z → Run i₀ L₁ (up z (Ω (toLv z)))) e (h y gy)))) where
    unup : Run i₀ L₁ (up (suc ω⁺T) (Ω (toLv (suc ω⁺T)))) → Run i₀ (toLv (suc ω⁺T)) (Ω (toLv (suc ω⁺T)))
    unup (ru q) = q
```

## §3 好输入类 `G` 的三个性质

**(i) `G` 不是规范的.** `ω` 与 `ω⁺` 值相同, 结构上互不可比. 所以含其中一个的好类不能含另一个, "选 `G`" 至少包含选基本列. 这条是树侧推出来的.

```agda
ω≇ω⁺ : ¬ (toLv ωT ≅ toLv ω⁺T)
ω≇ω⁺ (l≅ h) with h 0
... | ()

ω⊀ω⁺ : ¬ (toLv ωT ≺ toLv ω⁺T)
ω⊀ω⁺ (via (n , r) e) = lim≇nat (atNat (isNatT (suc n)) r) e

ω⁺⊀ω : ¬ (toLv ω⁺T ≺ toLv ωT)
ω⁺⊀ω (via (n , r) e) = lim≇nat (atNat (isNatT n) r) e
```

**(ii) 最小的类不能归纳地定义.** "由折叠输出生成" 的 `Gen` 与 `Run` 互递归时不严格正: `Gen` 的 `gψ` 带 `Run`, `Run` 的分支在箭头左边用 `Gen`. 编译器的回答是 `Run is not strictly positive` (试验文件没有保留, 因为它不能带 `--safe`). `Run` 对 `G` 又是混合变的 (`rc` 里 `G` 两边都出现), 所以非直谓定义也不解决.

**(iii) 分层后 `Close` 变成定义, 内容移到跨层.** 对 `n` 递归可以定义 `Gs n`, 于是 `close` 只是打包. 但 `rc` 的字段 `∀ x → G x → G (ψ (f x))` 要求同一层封闭, 而这种分层一步折叠就升一层. 判断: 这就是阶段塔在证书里的形态. 我没有证明别的分层都不行.

```agda
module Tower (D : Oracle) where
  open Fold D

  Gs : ℕ → ∀ {k} → Ordᴸ k → Set
  Gs zero    x = ⊤
  Gs (suc n) {k = i} x = Σ Lv λ k → Σ (Ordᴸ k) λ y → (ψ {i} y ≡ x) × Cert.Run D (Gs n) i k y

  close : ∀ n i k (y : Ordᴸ k) → Cert.Run D (Gs n) i k y → Gs (suc n) (ψ {i} y)
  close n i k y r = k , y , refl , r
```
