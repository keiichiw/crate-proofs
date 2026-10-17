# 既存報告・仕様の確認（2026-10-16）

対象は既存の最小再現と固定ツール。検索時点の公開 GitHub issue/PR とコメントを
読み、現行ローカルの停止箇所と比較した。最新版をビルドして再検証したわけではない。
issue の open は「最新版で再現すること」の独立した証明ではない。
検索語・取得した issue の状態は [upstream-search.json](upstream-search.json)。
外部への投稿・問い合わせはしていない。

## ipnet schema：不具合と判断する根拠を確認

IPNET-002（`a/64` を IPv6 schema が受理するが Deserialize は拒否）は、
**公式の Serde 互換性目標と導入意図から schema の不具合と判断する**。
以前の「仕様確認が必要」という留保を、この根拠付きの判断に更新する。

- [Schemars 0.8.22](https://docs.rs/schemars/0.8.22/schemars/#serde-compatibility) と
  [1.2.1](https://docs.rs/schemars/1.2.1/schemars/#serde-compatibility) は、
  生成 schema と serde_json の serialize/deserialize の対応を目標として明記する。
- ipnet [issue #40](https://github.com/krisprice/ipnet/issues/40) は、parser と
  Serde 表現に合わせるため手動 JsonSchema 実装を求めたもの。
  [PR #41](https://github.com/krisprice/ipnet/pull/41) が merged となり解決した。
  [管理者のコメント](https://github.com/krisprice/ipnet/issues/40#issuecomment-1100769670)
  でも修正として扱われている。
- 今回の正規表現は ipnet 自身の手動実装。`a/64` の受理は validator の誤動作ではなく、
  schema と対象型の受理範囲の不一致である。

ただし #40 の当時の直接的な問題は object/string の表現差。
これを「全入力について schema と parser が iff で一致するとの保証が公式に確認済み」
と拡大解釈しない。今回の `a/64` に対する管理者の見解は未取得。
現時点での適切な報告は「再現済みの不一致で、公開された互換性目標に反する検証不具合」。
これは新たな native 反例ではなく、既存反例の分類を裏付ける資料調査。

## Aeneas：結論

| 再現例 | 分類 | 既存報告との対応 |
|---|---|---|
| `mutable_dyn_write` | 可変 dyn cast の未実装。高い確度 | [PR #729](https://github.com/AeneasVerif/aeneas/pull/729) は preliminary support、主目的は Debug。関連 [#1343](https://github.com/AeneasVerif/aeneas/issues/1343) は open。ただし Box dyn の例であり今回の可変 cast と完全一致ではない |
| `next_ascii` / 借用 FnOnce | 生成コードの型不整合という実装不具合。背景は可変借用を含む高階関数への対応不足 | [#1046](https://github.com/AeneasVerif/aeneas/issues/1046) は open、同種の FnOnce 戻り状態不整合。既存例は closure の capture、今回は callback の可変引数なので厳密な重複とは未断定 |
| `extend_bytes` / Iterator signature | 型制約を処理する経路の不備・前処理との不整合によるクラッシュ。単なる Vec モデル未実装とは別 | [#1435](https://github.com/AeneasVerif/aeneas/issues/1435) が最も直接的な既存報告。同じ copied() と同じチェックで停止。[#1164](https://github.com/AeneasVerif/aeneas/issues/1164)、[#1222](https://github.com/AeneasVerif/aeneas/issues/1222) も同じ検査箇所の報告 |

### 可変 dyn：未実装と判断する根拠

固定 revision の `src/interp/InterpExpressions.ml` の unsize 処理は shared borrow
を処理する分岐を持つ一方、今回の mutable reference は既定の unsupported エラーへ落ちる。
PR #729 は merged であり、dyn 一般が全く未実装という意味ではない。
#1343 は dynamic type を持つ構造体という隣接領域の機能不足。
検索では `&mut Sink -> &mut dyn fmt::Write` と同じ最小例の issue は見つからなかった。
「未報告」と断言するのではなく、関連 issue に追加例として示す候補。

### FnOnce：不正な Lean の生成と機能不足の両面

`backends/lean/Aeneas/Std/Core/Ops.lean` の FnOnce モデルは
`Self → Args → Result Output`。今回の closure 本体は引数の更新も返す必要があり、
`Result (Option U8 × Cursor)` を生成するが、instance の型と一致しない。
機能を明示的に拒否するのでなく、抽出成功後に型検査不能なコードが出るため、
利用者向けには「translation bug」と報告するのが適切。
内部設計上は、可変借用を持つ Args/capture の状態返却を高階関数のモデルへ
接続する対応が不足している。単に1行の型を変えれば解決するとは主張しない。

#1046 本文と [追加の短い例](https://github.com/AeneasVerif/aeneas/issues/1046#issuecomment-5015034346)
も FnOnce 辞書と実装の返却状態が一致せず、同じ product-type エラーを起こす。
ただし borrowed argument と captured borrow の差があるので、同一原因の完全な証明ではない。
[#1437](https://github.com/AeneasVerif/aeneas/issues/1437) は iterator の backward result
欠落というさらに別の関連例。これらをすべて同一 issue としては扱わない。

### Iterator：既存報告との一致が強い

今回の `SymbolicToPureTypes.ml:1004–1005` は
`sg.item_binder_params.trait_type_constraints = []` という sanity check。
#1435 は `bytes.iter().copied()` だけで再現し、同じ関数・同じ検査で停止する。
#1164 の [調査コメント](https://github.com/AeneasVerif/aeneas/issues/1164#issuecomment-6214731320)
にもこの検査と #1222/#1435 の関係が記載されている。
従って今回の extend 例を新規独立バグとして出す必要性は低い。

処理不能な associated-type equality constraints が残ることが直接原因。
Charon が除去すべき制約を残すのか、Aeneas が受け入れて処理すべきかという責任分担は未確定。
「関連型一般が未実装」「Vec::extend の算法のバグ」とは判断できない。
少なくとも予期しない internal error で停止する実装・診断上の不具合であり、
広義にはこの型制約を扱う対応の不足も含む。

上記3ファイルの当該ローカル変更は `git diff` で空だった。
それでも実行環境全体には既存の互換パッチがあるため、公開時は
[再現 README](aeneas/README.md) の固定 revision とパッチ情報を添える。

## 報告する場合の扱い

- dyn：新規 feature request または #1343 に具体的な mutable-cast の追加例。
- FnOnce：まず #1046 に「mutable argument の別形状」として最小例を関連付ける。
- Iterator：まず #1435 を参照。#1164/#1222 に同じチェックの詳細があるため重複作成を避ける。

ここにあるのは報告先の判断材料であり、投稿はしていない。
