第0步先验（判断，另有 Pre.agda 最小实例已编译）
壁垒三前提逐条：1 精确 Ordᴰ 初始段未对本候选声称或提供；2 仍用原层号 L、塔、Λ，可供 Ω 分支，未通过换一个可数系统回避；3 明确放弃有界处处三歧。Rb 条目是 Maybe 的非严格字面路径二选一，既允许 nothing，也没有第三支相等；Pre.miss 在共同根 tw 3 的同一个非零孩子上返回 nothing。不能把它当 Ω-Extension.<ᴵ-dec。
开新行三问：1 受影响的是 inc c′ v 指定孩子行，不是 inu 一致目标行；2 表提供 Maybe ((h c′ ≤ h c) ⊎ (h c ≤ h c′))，不是 Maybe (c ≡ c′)，无全下标自反证据函数；3 不要求按层号相等/槽位存在保留，仍用旧 kp，表只由零构造子与已有 lift 路径填写。
obs→dec 核机制：viaE→dec 缺 Maybe 相等的 ViaE 数据，full→dec 缺完整性律；hand→wdec 缺全 Hand+Offᴾ，branch→wdec 缺折叠头部的 on/off。在表观察上，零对非零也返回 just，故不满足 off；非零对角返回 nothing，故不满足全 Same/on。零构造子自身可判是允许的有限观察。后续 YiCWCheck 将编译这些表侧失败；不外推为折叠输出头部上的否定。
字面公共界：每对 hᵗ n c 与 hᵗ n c′ 均有 inc c self / inc c′ self 通到 tw (suc n)。正条目由 lift 从 hᵗ n zero = tw n 通到 hᵗ n c，没有裸索引序律。
判决：允许继续此新候选；未得任何新值。
