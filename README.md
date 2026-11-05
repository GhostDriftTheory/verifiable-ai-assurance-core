# Formal Foundations of Verifiable AI Assurance

[![Lean verification](https://github.com/GhostDriftTheory/verifiable-ai-assurance-core/actions/workflows/lean-ci.yml/badge.svg)](https://github.com/GhostDriftTheory/verifiable-ai-assurance-core/actions/workflows/lean-ci.yml)

**AIの判断・実行を信頼する際、真正性・実行の適切さ・責任の追跡可能性のうち、何を検証できなければならないか。**

本リポジトリは、その問いを企業・製品・業界に依存しないLean 4の抽象モデルとして扱います。公開するのは、保証に必要な情報の区別、3領域の相補性、同じ対象についての情報合成、選択した区別の履歴への保存に関する形式理論です。業務システムの参照実装ではありません。

## 3つの保証能力

| 保証能力 | 問い |
|---|---|
| 情報の真正性 | 受け取った証拠の由来を信頼できるか。 |
| 実行の保証 | 対象の実行が、採用した条件を満たしているか。 |
| 責任の追跡可能性 | 判断や責任について、監査に必要な区別を保持しているか。 |

3つの**製品**を導入すべきという意味ではありません。一つの証明書やシステムが複数の能力を担う設計も含みます。また、発行元の真正性と、発行元が述べた内容の現実世界での真実性は区別します。［3］

## 中心となる形式化

**必要性。** 正常な事例と不適切な事例を同じ観測に潰してしまう検証者は、誤受入を防ぎながらその正常事例を受け入れることができません。この結果は「すべて拒否すれば安全」という空虚な結論を避けます。4つの抽象事例を使い、3領域のどれを省略してもこの問題が生じる反例を示します。

**条件付きの十分性。** 保証目標を観測の仕組みとは別に与え、各領域の観測が必要な事実の区別を保持し、3領域がその目標を網羅するという明示的な前提の下で、結合観測から目標を正確に判定できることを扱います。網羅性は、モデルを作っただけで成立したことにはしません。

**企業間の引継ぎと監査。** 公開済みResponsibility OSの `PreservesPolicy` に直接接続し、個別事例の必要な区別を保持することと、それらを並べた有限履歴の区別を保持することの対応を形式化します。［4］

主要定理は次のとおりです。すべて `VerifiableAIAssurance` 名前空間にあります。

| Lean識別子 | 対象 |
|---|---|
| `sufficient_iff_exact_judge` | 正確な判定が可能であるための必要十分な情報条件。 |
| `sound_useful_judge_must_separate` | 誤受入防止と有用な受入の両立には、正常・不適切な事例の区別が必要。 |
| `covered_joint_view_is_sufficient` | 各領域の情報の十分性と目標の網羅性を前提とした結合の十分性。 |
| `Independence.three_capability_information_result` | 正常事例の存在、結合の十分性、各領域を省略した場合の不十分性。 |
| `separate_local_successes_need_not_have_a_common_case` | 別々の対象について成立した主張を、同一対象の保証と混同できないこと。 |
| `kernel_policy_iff_selected_distinctions` | 公開済み責任OSの観測ポリシーとの直接的な対応。 |
| `joint_information_preserves_selected_history` | 選んだ保証目標の区別を有限履歴にも保持すること。 |
| `PublicGateway.published_commit_yields_execution_evidence` | 公開済みGatewayの定理から、受理済み実行の証拠を取り出せること。 |

Gatewayとの接続は、すでに公開されている定理の系です。新しい統合アダプターや実行方式を提供するものではありません。Gateway側の信頼前提も引き継ぎます。［5］

## 適用範囲

EU AI Actや広島AIプロセスを背景に、検証可能な保証をどのように考えるかを扱う基礎研究です。法令や政策の全要求を3領域で網羅したとの証明、公式な適合認証、実システム全体の安全性を意味しません。［1］［2］

「必要十分」は**固定した保証目標と観測モデル**に関する主張です。追加の要件が、現在の観測では区別できない事例を区別する必要があるなら、追加情報が必要になることも形式化しています。

公開対象は抽象的な定義・定理・反例と、既存公開理論への接続です。取引データ形式、具体的な証拠照合手順、実行制御、運用状態管理、暗号検証、通信仕様、接続アダプターは含みません。履歴を扱う箇所も数学的な列の議論であり、保存・復元の運用方式ではありません。

## 検証

**本配布時点では、Leanコンパイルと公理監査の成功は未確認です。** 検証の根拠は、各コミットに対するGitHub Actionsの実行結果とログです。設定ファイルの存在やバッジの掲載だけを検証成功とは扱いません。

GitHubへのpush、pull request、手動実行で次を行います。

1. 公開ファイルが宣言した6ファイルのみであることを確認する。
2. 公開済みの2カーネルを固定コミットから取得し、Git blobハッシュを照合する。
3. Lean 4.26.0と固定依存関係でビルドし、Leanファイルを再実行して公理監査を行う。

公理監査では、本リポジトリの名前空間にある定理を検査します。抽象理論にはLeanの通常の論理公理のみを許可し、`PublicGateway` 内の定理に限り、既存Gatewayの明示した信頼前提を追加で許可します。未許可の依存があれば処理は失敗します。検証ログには、コミット、コンパイラ版、ソースハッシュも記録します。

ローカルで再現する場合は、ワークフローの「Retrieve the exact already-public kernel sources」の取得・照合処理を同じ作業ディレクトリで実行した後、次を実行します。Git、curl、elanが必要です。

```bash
lake exe cache get Mathlib.CategoryTheory.Grothendieck Mathlib.CategoryTheory.Adjunction.Basic Mathlib.CategoryTheory.Functor.FullyFaithful
lake build
lake env lean VerifiableAIAssurance.lean
```

取得された2つの公開ソースと `.lake/`、検証ログはビルド用であり、このリポジトリに追加してコミットする対象ではありません。公開ソースの指定は次のとおりです。

| モジュール | 固定コミット | Git blob |
|---|---|---|
| `ResponsibilityOS.lean` | `3416b4f542addcfdf2ac8304c04d1d69bdbcfbf5` | `34bdac79ffdba54d8464daca4a5ed6ae21e2abd5` |
| `adic_cyber_assurance_gateway.lean` | `b539f21bd94db715925f2c33fce99a54c4b9d261` | `b7ed90059b4b34e9b753919c23263ddd124b81d1` |

## ファイル構成

```text
VerifiableAIAssurance.lean       抽象モデル・定理・公理監査
README.md                       説明・適用範囲・検証方法
lakefile.lean                   ビルド設定
lean-toolchain                  Lean版の固定
lake-manifest.json              依存関係の固定
.github/workflows/lean-ci.yml    自動検証
```

## 一次資料・公開理論

［1］European Commission, AI Act Service Desk, Article 12: Record-keeping.
https://ai-act-service-desk.ec.europa.eu/en/ai-act/article-12

［2］外務省、G7 Leaders' Statement on the Hiroshima AI Process（国際指針・国際行動規範を含む公開ページ、2023年10月30日）。
https://www.mofa.go.jp/ecm/ec/page5e_000076.html

［3］W3C, Verifiable Credentials Data Model v2.0.
https://www.w3.org/TR/vc-data-model-2.0/

［4］Responsibility OS Kernel.
https://github.com/GhostDriftTheory/responsibility-os-kernel

［5］ADIC Cyber Assurance Gateway.
https://github.com/GhostDriftTheory/adic-cyber-assurance-gateway

## 権利

株式会社AIアシュアランス。本文・追加コードについて、本リポジトリでは新たなOSSライセンスまたは特許実施許諾を付与していません。参照する既存ソースと外部依存関係には、それぞれの権利条件が適用されます。
