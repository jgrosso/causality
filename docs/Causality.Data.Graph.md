---
title: Causality.Data.Graph
---

Definitions and proofs about (directed, acyclic, simple, etc.) graphs.

<pre class="Agda"><a id="118" class="Keyword">module</a> <a id="125" href="Causality.Data.Graph.html" class="Module">Causality.Data.Graph</a> <a id="146" class="Keyword">where</a>

<a id="153" class="Keyword">open</a> <a id="158" class="Keyword">import</a> <a id="165" href="Data.Fin.html" class="Module">Data.Fin</a> <a id="174" class="Keyword">using</a> <a id="180" class="Symbol">(</a><a id="181" href="Data.Fin.Base.html#1126" class="Datatype">Fin</a><a id="184" class="Symbol">)</a>
<a id="186" class="Keyword">open</a> <a id="191" class="Keyword">import</a> <a id="198" href="Data.List.html" class="Module">Data.List</a> <a id="208" class="Keyword">using</a> <a id="214" class="Symbol">(</a><a id="215" href="Agda.Builtin.List.html#130" class="Datatype">List</a><a id="219" class="Symbol">;</a> <a id="221" href="Data.List.Base.html#8092" class="Function">filter</a><a id="227" class="Symbol">)</a>
<a id="229" class="Keyword">open</a> <a id="234" class="Keyword">import</a> <a id="241" href="Data.List.Relation.Unary.Linked.html" class="Module">Data.List.Relation.Unary.Linked</a> <a id="273" class="Keyword">using</a> <a id="279" class="Symbol">(</a><a id="280" href="Data.List.Relation.Unary.Linked.html#1390" class="Datatype">Linked</a><a id="286" class="Symbol">)</a>
<a id="288" class="Keyword">open</a> <a id="293" class="Keyword">import</a> <a id="300" href="Data.List.Relation.Unary.Unique.Propositional.html" class="Module">Data.List.Relation.Unary.Unique.Propositional</a> <a id="346" class="Keyword">using</a> <a id="352" class="Symbol">(</a><a id="353" href="Data.List.Relation.Unary.Unique.Setoid.html#719" class="Datatype">Unique</a><a id="359" class="Symbol">)</a>
<a id="361" class="Keyword">import</a> <a id="368" href="Data.List.Relation.Unary.Unique.Propositional.Properties.html" class="Module">Data.List.Relation.Unary.Unique.Propositional.Properties</a> <a id="425" class="Symbol">as</a> <a id="428" class="Module">Unique</a>
<a id="435" class="Keyword">open</a> <a id="440" class="Keyword">import</a> <a id="447" href="Data.Nat.html" class="Module">Data.Nat</a> <a id="456" class="Keyword">using</a> <a id="462" class="Symbol">(</a><a id="463" href="Agda.Builtin.Nat.html#186" class="Datatype">ℕ</a><a id="464" class="Symbol">)</a>
<a id="466" class="Keyword">open</a> <a id="471" class="Keyword">import</a> <a id="478" href="Data.Product.html" class="Module">Data.Product</a> <a id="491" class="Keyword">using</a> <a id="497" class="Symbol">(</a><a id="498" href="Data.Product.html#1369" class="Function">∃</a><a id="499" class="Symbol">;</a> <a id="501" href="Data.Product.html#1167" class="Function Operator">_×_</a><a id="504" class="Symbol">;</a> <a id="506" href="Agda.Builtin.Sigma.html#218" class="InductiveConstructor Operator">_,_</a><a id="509" class="Symbol">)</a> <a id="511" class="Keyword">renaming</a> <a id="520" class="Symbol">(</a><a id="521" href="Agda.Builtin.Sigma.html#234" class="Field">proj₁</a> <a id="527" class="Symbol">to</a> <a id="530" class="Field">_₁</a><a id="532" class="Symbol">)</a>
<a id="534" class="Keyword">open</a> <a id="539" class="Keyword">import</a> <a id="546" href="Data.Sum.html" class="Module">Data.Sum</a> <a id="555" class="Keyword">using</a> <a id="561" class="Symbol">(</a><a id="562" href="Data.Sum.Base.html#734" class="Datatype Operator">_⊎_</a><a id="565" class="Symbol">)</a>
<a id="567" class="Keyword">open</a> <a id="572" class="Keyword">import</a> <a id="579" href="Function.html" class="Module">Function</a> <a id="588" class="Keyword">using</a> <a id="594" class="Symbol">(</a><a id="595" href="Function.Base.html#1031" class="Function Operator">_∘_</a><a id="598" class="Symbol">;</a> <a id="600" href="Function.Base.html#1554" class="Function">flip</a><a id="604" class="Symbol">)</a>
<a id="606" class="Keyword">open</a> <a id="611" class="Keyword">import</a> <a id="618" href="Relation.Unary.html" class="Module">Relation.Unary</a> <a id="633" class="Keyword">using</a> <a id="639" class="Symbol">(</a><a id="640" href="Relation.Unary.html#3536" class="Function">Decidable</a><a id="649" class="Symbol">)</a>

<a id="652" class="Keyword">record</a> <a id="DirectedMultigraph"></a><a id="659" href="Causality.Data.Graph.html#659" class="Record">DirectedMultigraph</a> <a id="678" class="Symbol">:</a> <a id="680" href="Agda.Primitive.html#320" class="Primitive">Set</a> <a id="684" class="Keyword">where</a>
  <a id="692" class="Keyword">field</a> <a id="DirectedMultigraph.|V|"></a><a id="698" href="Causality.Data.Graph.html#698" class="Field">|V|</a> <a id="702" class="Symbol">:</a> <a id="704" href="Agda.Builtin.Nat.html#186" class="Datatype">ℕ</a>

  <a id="DirectedMultigraph.V"></a><a id="709" href="Causality.Data.Graph.html#709" class="Function">V</a> <a id="711" class="Symbol">:</a> <a id="713" href="Agda.Primitive.html#320" class="Primitive">Set</a>
  <a id="719" href="Causality.Data.Graph.html#709" class="Function">V</a> <a id="721" class="Symbol">=</a> <a id="723" href="Data.Fin.Base.html#1126" class="Datatype">Fin</a> <a id="727" href="Causality.Data.Graph.html#698" class="Field">|V|</a>

  <a id="DirectedMultigraph.Edge"></a><a id="734" href="Causality.Data.Graph.html#734" class="Function">Edge</a> <a id="739" class="Symbol">:</a> <a id="741" href="Agda.Primitive.html#320" class="Primitive">Set</a>
  <a id="747" href="Causality.Data.Graph.html#734" class="Function">Edge</a> <a id="752" class="Symbol">=</a> <a id="754" href="Causality.Data.Graph.html#709" class="Function">V</a> <a id="756" href="Data.Product.html#1167" class="Function Operator">×</a> <a id="758" href="Causality.Data.Graph.html#709" class="Function">V</a>

  <a id="763" class="Keyword">field</a> <a id="DirectedMultigraph.E"></a><a id="769" href="Causality.Data.Graph.html#769" class="Field">E</a> <a id="771" class="Symbol">:</a> <a id="773" href="Agda.Builtin.List.html#130" class="Datatype">List</a> <a id="778" href="Causality.Data.Graph.html#734" class="Function">Edge</a>

  <a id="DirectedMultigraph._∃⟶_"></a><a id="786" href="Causality.Data.Graph.html#786" class="Function Operator">_∃⟶_</a> <a id="791" class="Symbol">:</a> <a id="793" class="Symbol">(</a><a id="794" href="Causality.Data.Graph.html#794" class="Bound">i</a> <a id="796" href="Causality.Data.Graph.html#796" class="Bound">j</a> <a id="798" class="Symbol">:</a> <a id="800" href="Causality.Data.Graph.html#709" class="Function">V</a><a id="801" class="Symbol">)</a> <a id="803" class="Symbol">→</a> <a id="805" href="Agda.Primitive.html#320" class="Primitive">Set</a>
  <a id="811" href="Causality.Data.Graph.html#811" class="Bound">i</a> <a id="813" href="Causality.Data.Graph.html#786" class="Function Operator">∃⟶</a> <a id="816" href="Causality.Data.Graph.html#816" class="Bound">j</a> <a id="818" class="Symbol">=</a> <a id="820" class="Symbol">(</a><a id="821" href="Causality.Data.Graph.html#811" class="Bound">i</a> <a id="823" href="Agda.Builtin.Sigma.html#218" class="InductiveConstructor Operator">,</a> <a id="825" href="Causality.Data.Graph.html#816" class="Bound">j</a><a id="826" class="Symbol">)</a> <a id="828" href="Data.List.Membership.Setoid.html#887" class="Function Operator">∈</a> <a id="830" href="Causality.Data.Graph.html#769" class="Field">E</a>
    <a id="836" class="Keyword">where</a> <a id="842" class="Keyword">open</a> <a id="847" class="Keyword">import</a> <a id="854" href="Data.List.Membership.Propositional.html" class="Module">Data.List.Membership.Propositional</a> <a id="889" class="Keyword">using</a> <a id="895" class="Symbol">(</a><a id="896" href="Data.List.Membership.Setoid.html#887" class="Function Operator">_∈_</a><a id="899" class="Symbol">)</a>

  <a id="DirectedMultigraph._∃⟵_"></a><a id="904" href="Causality.Data.Graph.html#904" class="Function Operator">_∃⟵_</a> <a id="909" class="Symbol">:</a> <a id="911" class="Symbol">(</a><a id="912" href="Causality.Data.Graph.html#912" class="Bound">i</a> <a id="914" href="Causality.Data.Graph.html#914" class="Bound">j</a> <a id="916" class="Symbol">:</a> <a id="918" href="Causality.Data.Graph.html#709" class="Function">V</a><a id="919" class="Symbol">)</a> <a id="921" class="Symbol">→</a> <a id="923" href="Agda.Primitive.html#320" class="Primitive">Set</a>
  <a id="929" href="Causality.Data.Graph.html#904" class="Function Operator">_∃⟵_</a> <a id="934" class="Symbol">=</a> <a id="936" href="Function.Base.html#1554" class="Function">flip</a> <a id="941" href="Causality.Data.Graph.html#786" class="Function Operator">_∃⟶_</a>

  <a id="DirectedMultigraph._∃——_"></a><a id="949" href="Causality.Data.Graph.html#949" class="Function Operator">_∃——_</a> <a id="955" class="Symbol">:</a> <a id="957" class="Symbol">(</a><a id="958" href="Causality.Data.Graph.html#958" class="Bound">i</a> <a id="960" href="Causality.Data.Graph.html#960" class="Bound">j</a> <a id="962" class="Symbol">:</a> <a id="964" href="Causality.Data.Graph.html#709" class="Function">V</a><a id="965" class="Symbol">)</a> <a id="967" class="Symbol">→</a> <a id="969" href="Agda.Primitive.html#320" class="Primitive">Set</a>
  <a id="975" href="Causality.Data.Graph.html#975" class="Bound">i</a> <a id="977" href="Causality.Data.Graph.html#949" class="Function Operator">∃——</a> <a id="981" href="Causality.Data.Graph.html#981" class="Bound">j</a> <a id="983" class="Symbol">=</a> <a id="985" href="Causality.Data.Graph.html#975" class="Bound">i</a> <a id="987" href="Causality.Data.Graph.html#786" class="Function Operator">∃⟶</a> <a id="990" href="Causality.Data.Graph.html#981" class="Bound">j</a> <a id="992" href="Data.Sum.Base.html#734" class="Datatype Operator">⊎</a> <a id="994" href="Causality.Data.Graph.html#981" class="Bound">j</a> <a id="996" href="Causality.Data.Graph.html#786" class="Function Operator">∃⟶</a> <a id="999" href="Causality.Data.Graph.html#975" class="Bound">i</a>

  <a id="DirectedMultigraph.DirectedPath"></a><a id="1004" href="Causality.Data.Graph.html#1004" class="Function">DirectedPath</a> <a id="1017" class="Symbol">:</a> <a id="1019" href="Agda.Builtin.List.html#130" class="Datatype">List</a> <a id="1024" href="Causality.Data.Graph.html#709" class="Function">V</a> <a id="1026" class="Symbol">→</a> <a id="1028" href="Agda.Primitive.html#320" class="Primitive">Set</a>
  <a id="1034" href="Causality.Data.Graph.html#1004" class="Function">DirectedPath</a> <a id="1047" class="Symbol">=</a> <a id="1049" href="Data.List.Relation.Unary.Linked.html#1390" class="Datatype">Linked</a> <a id="1056" href="Causality.Data.Graph.html#786" class="Function Operator">_∃⟶_</a>

  <a id="DirectedMultigraph.UndirectedPath"></a><a id="1064" href="Causality.Data.Graph.html#1064" class="Function">UndirectedPath</a> <a id="1079" class="Symbol">:</a> <a id="1081" href="Agda.Builtin.List.html#130" class="Datatype">List</a> <a id="1086" href="Causality.Data.Graph.html#709" class="Function">V</a> <a id="1088" class="Symbol">→</a> <a id="1090" href="Agda.Primitive.html#320" class="Primitive">Set</a>
  <a id="1096" href="Causality.Data.Graph.html#1064" class="Function">UndirectedPath</a> <a id="1111" class="Symbol">=</a> <a id="1113" href="Data.List.Relation.Unary.Linked.html#1390" class="Datatype">Linked</a> <a id="1120" href="Causality.Data.Graph.html#949" class="Function Operator">_∃——_</a>

  <a id="DirectedMultigraph.acyclic-path"></a><a id="1129" href="Causality.Data.Graph.html#1129" class="Function">acyclic-path</a> <a id="1142" class="Symbol">:</a> <a id="1144" href="Data.Product.html#1369" class="Function">∃</a> <a id="1146" href="Causality.Data.Graph.html#1004" class="Function">DirectedPath</a> <a id="1159" class="Symbol">→</a> <a id="1161" href="Agda.Primitive.html#320" class="Primitive">Set</a>
  <a id="1167" href="Causality.Data.Graph.html#1129" class="Function">acyclic-path</a> <a id="1180" class="Symbol">=</a> <a id="1182" href="Data.List.Relation.Unary.Unique.Setoid.html#719" class="Datatype">Unique</a> <a id="1189" href="Function.Base.html#1031" class="Function Operator">∘</a> <a id="1191" href="Causality.Data.Graph.html#530" class="Field Operator">_₁</a>

  <a id="DirectedMultigraph.FilterEdges"></a><a id="1197" href="Causality.Data.Graph.html#1197" class="Function">FilterEdges</a> <a id="1209" class="Symbol">:</a> <a id="1211" class="Symbol">∀</a> <a id="1213" class="Symbol">{</a><a id="1214" href="Causality.Data.Graph.html#1214" class="Bound">p</a> <a id="1216" href="Causality.Data.Graph.html#1216" class="Bound">a</a><a id="1217" class="Symbol">}</a> <a id="1219" class="Symbol">→</a> <a id="1221" href="Agda.Primitive.html#320" class="Primitive">Set</a> <a id="1225" href="Causality.Data.Graph.html#1216" class="Bound">a</a> <a id="1227" class="Symbol">→</a> <a id="1229" href="Agda.Primitive.html#320" class="Primitive">Set</a> <a id="1233" class="Symbol">_</a>
  <a id="1237" href="Causality.Data.Graph.html#1197" class="Function">FilterEdges</a> <a id="1249" class="Symbol">{</a><a id="1250" href="Causality.Data.Graph.html#1250" class="Bound">p</a><a id="1251" class="Symbol">}</a> <a id="1253" href="Causality.Data.Graph.html#1253" class="Bound">Self</a> <a id="1258" class="Symbol">=</a> <a id="1260" class="Symbol">{</a><a id="1261" href="Causality.Data.Graph.html#1261" class="Bound">P</a> <a id="1263" class="Symbol">:</a> <a id="1265" href="Causality.Data.Graph.html#734" class="Function">Edge</a> <a id="1270" class="Symbol">→</a> <a id="1272" href="Agda.Primitive.html#320" class="Primitive">Set</a> <a id="1276" href="Causality.Data.Graph.html#1250" class="Bound">p</a><a id="1277" class="Symbol">}</a> <a id="1279" class="Symbol">→</a> <a id="1281" href="Relation.Unary.html#3536" class="Function">Decidable</a> <a id="1291" href="Causality.Data.Graph.html#1261" class="Bound">P</a> <a id="1293" class="Symbol">→</a> <a id="1295" href="Causality.Data.Graph.html#1253" class="Bound">Self</a>

  <a id="DirectedMultigraph.filter-edges"></a><a id="1303" href="Causality.Data.Graph.html#1303" class="Function">filter-edges</a> <a id="1316" class="Symbol">:</a> <a id="1318" class="Symbol">∀</a> <a id="1320" class="Symbol">{</a><a id="1321" href="Causality.Data.Graph.html#1321" class="Bound">p</a><a id="1322" class="Symbol">}</a> <a id="1324" class="Symbol">→</a> <a id="1326" href="Causality.Data.Graph.html#1197" class="Function">FilterEdges</a> <a id="1338" class="Symbol">{</a><a id="1339" href="Causality.Data.Graph.html#1321" class="Bound">p</a><a id="1340" class="Symbol">}</a> <a id="1342" class="Symbol">_</a>
  <a id="1346" href="Causality.Data.Graph.html#1303" class="Function">filter-edges</a> <a id="1359" href="Causality.Data.Graph.html#1359" class="Bound">P?</a> <a id="1362" class="Symbol">=</a> <a id="1364" class="Keyword">record</a>
    <a id="1375" class="Symbol">{</a> <a id="1377" href="Causality.Data.Graph.html#698" class="Field">|V|</a> <a id="1381" class="Symbol">=</a> <a id="1383" href="Causality.Data.Graph.html#698" class="Field">|V|</a>
    <a id="1391" class="Symbol">;</a>  <a id="1394" href="Causality.Data.Graph.html#769" class="Field">E</a>  <a id="1397" class="Symbol">=</a> <a id="1399" href="Data.List.Base.html#8092" class="Function">filter</a> <a id="1406" href="Causality.Data.Graph.html#1359" class="Bound">P?</a> <a id="1409" href="Causality.Data.Graph.html#769" class="Field">E</a>
    <a id="1415" class="Symbol">}</a>


<a id="1419" class="Keyword">module</a> <a id="1426" href="Causality.Data.Graph.html#1426" class="Module">_</a> <a id="1428" class="Symbol">{</a><a id="1429" href="Causality.Data.Graph.html#1429" class="Bound">g</a> <a id="1431" class="Symbol">:</a> <a id="1433" href="Causality.Data.Graph.html#659" class="Record">DirectedMultigraph</a><a id="1451" class="Symbol">}</a> <a id="1453" class="Keyword">where</a>

  <a id="1462" class="Keyword">open</a> <a id="1467" class="Keyword">import</a> <a id="1474" href="Data.List.Relation.Unary.Any.Properties.html" class="Module">Data.List.Relation.Unary.Any.Properties</a> <a id="1514" class="Keyword">using</a> <a id="1520" class="Symbol">(</a><a id="1521" href="Data.List.Relation.Unary.Any.Properties.html#19858" class="Function">filter⁻</a><a id="1528" class="Symbol">)</a>
  <a id="1532" class="Keyword">open</a> <a id="1537" href="Causality.Data.Graph.html#659" class="Module">DirectedMultigraph</a>
  <a id="1558" class="Keyword">open</a> <a id="1563" href="Data.List.Relation.Unary.Linked.html#1390" class="Module">Linked</a>
  <a id="1572" class="Keyword">open</a> <a id="1577" class="Keyword">import</a> <a id="1584" href="Relation.Unary.html" class="Module">Relation.Unary</a> <a id="1599" class="Keyword">using</a> <a id="1605" class="Symbol">(</a><a id="1606" href="Relation.Unary.html#1742" class="Function Operator">_⊆_</a><a id="1609" class="Symbol">)</a>

  <a id="1614" href="Causality.Data.Graph.html#1614" class="Function">filter-edges-removes-paths</a> <a id="1641" class="Symbol">:</a> <a id="1643" class="Symbol">∀</a> <a id="1645" class="Symbol">{</a><a id="1646" href="Causality.Data.Graph.html#1646" class="Bound">p</a><a id="1647" class="Symbol">}</a> <a id="1649" class="Symbol">{</a><a id="1650" href="Causality.Data.Graph.html#1650" class="Bound">P</a> <a id="1652" class="Symbol">:</a> <a id="1654" href="Causality.Data.Graph.html#734" class="Function">Edge</a> <a id="1659" href="Causality.Data.Graph.html#1429" class="Bound">g</a> <a id="1661" class="Symbol">→</a> <a id="1663" href="Agda.Primitive.html#320" class="Primitive">Set</a> <a id="1667" href="Causality.Data.Graph.html#1646" class="Bound">p</a><a id="1668" class="Symbol">}</a> <a id="1670" class="Symbol">{</a><a id="1671" href="Causality.Data.Graph.html#1671" class="Bound">P?</a> <a id="1674" class="Symbol">:</a> <a id="1676" href="Relation.Unary.html#3536" class="Function">Decidable</a> <a id="1686" href="Causality.Data.Graph.html#1650" class="Bound">P</a><a id="1687" class="Symbol">}</a>
    <a id="1693" class="Symbol">→</a> <a id="1695" href="Causality.Data.Graph.html#1004" class="Function">DirectedPath</a> <a id="1708" class="Symbol">(</a><a id="1709" href="Causality.Data.Graph.html#1303" class="Function">filter-edges</a> <a id="1722" href="Causality.Data.Graph.html#1429" class="Bound">g</a> <a id="1724" href="Causality.Data.Graph.html#1671" class="Bound">P?</a><a id="1726" class="Symbol">)</a> <a id="1728" href="Relation.Unary.html#1742" class="Function Operator">⊆</a> <a id="1730" href="Causality.Data.Graph.html#1004" class="Function">DirectedPath</a> <a id="1743" href="Causality.Data.Graph.html#1429" class="Bound">g</a>
  <a id="1747" href="Causality.Data.Graph.html#1614" class="Function">filter-edges-removes-paths</a> <a id="1774" href="Data.List.Relation.Unary.Linked.html#1442" class="InductiveConstructor">[]</a>       <a id="1783" class="Symbol">=</a> <a id="1785" href="Data.List.Relation.Unary.Linked.html#1442" class="InductiveConstructor">[]</a>
  <a id="1790" href="Causality.Data.Graph.html#1614" class="Function">filter-edges-removes-paths</a> <a id="1817" href="Data.List.Relation.Unary.Linked.html#1462" class="InductiveConstructor">[-]</a>      <a id="1826" class="Symbol">=</a> <a id="1828" href="Data.List.Relation.Unary.Linked.html#1462" class="InductiveConstructor">[-]</a>
  <a id="1834" href="Causality.Data.Graph.html#1614" class="Function">filter-edges-removes-paths</a> <a id="1861" class="Symbol">(</a><a id="1862" href="Causality.Data.Graph.html#1862" class="Bound">p</a> <a id="1864" href="Data.List.Relation.Unary.Linked.html#1496" class="InductiveConstructor Operator">∷</a> <a id="1866" href="Causality.Data.Graph.html#1866" class="Bound">p′</a><a id="1868" class="Symbol">)</a> <a id="1870" class="Symbol">=</a> <a id="1872" href="Data.List.Relation.Unary.Any.Properties.html#19858" class="Function">filter⁻</a> <a id="1880" class="Symbol">_</a> <a id="1882" href="Causality.Data.Graph.html#1862" class="Bound">p</a> <a id="1884" href="Data.List.Relation.Unary.Linked.html#1496" class="InductiveConstructor Operator">∷</a> <a id="1886" href="Causality.Data.Graph.html#1614" class="Function">filter-edges-removes-paths</a> <a id="1913" href="Causality.Data.Graph.html#1866" class="Bound">p′</a>


<a id="1918" class="Keyword">record</a> <a id="DirectedGraph"></a><a id="1925" href="Causality.Data.Graph.html#1925" class="Record">DirectedGraph</a> <a id="1939" class="Symbol">:</a> <a id="1941" href="Agda.Primitive.html#320" class="Primitive">Set</a> <a id="1945" class="Keyword">where</a>
  <a id="1953" class="Keyword">field</a> <a id="DirectedGraph.base"></a><a id="1959" href="Causality.Data.Graph.html#1959" class="Field">base</a> <a id="1964" class="Symbol">:</a> <a id="1966" href="Causality.Data.Graph.html#659" class="Record">DirectedMultigraph</a>
  <a id="1987" class="Keyword">open</a> <a id="1992" href="Causality.Data.Graph.html#659" class="Module">DirectedMultigraph</a> <a id="2011" href="Causality.Data.Graph.html#1959" class="Field">base</a> <a id="2016" class="Keyword">hiding</a> <a id="2023" class="Symbol">(</a><a id="2024" href="Causality.Data.Graph.html#1303" class="Function">filter-edges</a><a id="2036" class="Symbol">)</a> <a id="2038" class="Keyword">public</a>

  <a id="2048" class="Keyword">field</a> <a id="DirectedGraph.simple"></a><a id="2054" href="Causality.Data.Graph.html#2054" class="Field">simple</a> <a id="2061" class="Symbol">:</a> <a id="2063" href="Data.List.Relation.Unary.Unique.Setoid.html#719" class="Datatype">Unique</a> <a id="2070" href="Causality.Data.Graph.html#769" class="Function">E</a>

  <a id="DirectedGraph.filter-edges"></a><a id="2075" href="Causality.Data.Graph.html#2075" class="Function">filter-edges</a> <a id="2088" class="Symbol">:</a> <a id="2090" class="Symbol">∀</a> <a id="2092" class="Symbol">{</a><a id="2093" href="Causality.Data.Graph.html#2093" class="Bound">p</a><a id="2094" class="Symbol">}</a> <a id="2096" class="Symbol">→</a> <a id="2098" href="Causality.Data.Graph.html#1197" class="Function">FilterEdges</a> <a id="2110" class="Symbol">{</a><a id="2111" href="Causality.Data.Graph.html#2093" class="Bound">p</a><a id="2112" class="Symbol">}</a> <a id="2114" class="Symbol">_</a>
  <a id="2118" href="Causality.Data.Graph.html#2075" class="Function">filter-edges</a> <a id="2131" href="Causality.Data.Graph.html#2131" class="Bound">f</a> <a id="2133" class="Symbol">=</a> <a id="2135" class="Keyword">record</a>
    <a id="2146" class="Symbol">{</a> <a id="2148" href="Causality.Data.Graph.html#1959" class="Field">base</a>   <a id="2155" class="Symbol">=</a> <a id="2157" href="Causality.Data.Graph.html#1303" class="Function">DirectedMultigraph.filter-edges</a> <a id="2189" href="Causality.Data.Graph.html#1959" class="Field">base</a> <a id="2194" href="Causality.Data.Graph.html#2131" class="Bound">f</a>
    <a id="2200" class="Symbol">;</a> <a id="2202" href="Causality.Data.Graph.html#2054" class="Field">simple</a> <a id="2209" class="Symbol">=</a> <a id="2211" href="Data.List.Relation.Unary.Unique.Propositional.Properties.html#4942" class="Function">Unique.filter⁺</a> <a id="2226" href="Causality.Data.Graph.html#2131" class="Bound">f</a> <a id="2228" href="Causality.Data.Graph.html#2054" class="Field">simple</a>
    <a id="2239" class="Symbol">}</a>


<a id="2243" class="Keyword">record</a> <a id="DAG"></a><a id="2250" href="Causality.Data.Graph.html#2250" class="Record">DAG</a> <a id="2254" class="Symbol">:</a> <a id="2256" href="Agda.Primitive.html#320" class="Primitive">Set</a> <a id="2260" class="Keyword">where</a>
  <a id="2268" class="Keyword">field</a> <a id="DAG.base"></a><a id="2274" href="Causality.Data.Graph.html#2274" class="Field">base</a> <a id="2279" class="Symbol">:</a> <a id="2281" href="Causality.Data.Graph.html#1925" class="Record">DirectedGraph</a>
  <a id="2297" class="Keyword">open</a> <a id="2302" href="Causality.Data.Graph.html#1925" class="Module">DirectedGraph</a> <a id="2316" href="Causality.Data.Graph.html#2274" class="Field">base</a> <a id="2321" class="Keyword">hiding</a> <a id="2328" class="Symbol">(</a><a id="2329" href="Causality.Data.Graph.html#1959" class="Field">base</a><a id="2333" class="Symbol">;</a> <a id="2335" href="Causality.Data.Graph.html#2075" class="Function">filter-edges</a><a id="2347" class="Symbol">)</a> <a id="2349" class="Keyword">public</a>

  <a id="2359" class="Keyword">field</a> <a id="DAG.acyclic"></a><a id="2365" href="Causality.Data.Graph.html#2365" class="Field">acyclic</a> <a id="2373" class="Symbol">:</a> <a id="2375" class="Symbol">(</a><a id="2376" href="Causality.Data.Graph.html#2376" class="Bound">p</a> <a id="2378" class="Symbol">:</a> <a id="2380" href="Data.Product.html#1369" class="Function">∃</a> <a id="2382" href="Causality.Data.Graph.html#1004" class="Function">DirectedPath</a><a id="2394" class="Symbol">)</a> <a id="2396" class="Symbol">→</a> <a id="2398" href="Causality.Data.Graph.html#1129" class="Function">acyclic-path</a> <a id="2411" href="Causality.Data.Graph.html#2376" class="Bound">p</a>

  <a id="DAG.filter-edges"></a><a id="2416" href="Causality.Data.Graph.html#2416" class="Function">filter-edges</a> <a id="2429" class="Symbol">:</a> <a id="2431" class="Symbol">∀</a> <a id="2433" class="Symbol">{</a><a id="2434" href="Causality.Data.Graph.html#2434" class="Bound">p</a><a id="2435" class="Symbol">}</a> <a id="2437" class="Symbol">→</a> <a id="2439" href="Causality.Data.Graph.html#1197" class="Function">FilterEdges</a> <a id="2451" class="Symbol">{</a><a id="2452" href="Causality.Data.Graph.html#2434" class="Bound">p</a><a id="2453" class="Symbol">}</a> <a id="2455" class="Symbol">_</a>
  <a id="2459" href="Causality.Data.Graph.html#2416" class="Function">filter-edges</a> <a id="2472" href="Causality.Data.Graph.html#2472" class="Bound">f</a> <a id="2474" class="Symbol">=</a> <a id="2476" class="Keyword">record</a>
    <a id="2487" class="Symbol">{</a> <a id="2489" href="Causality.Data.Graph.html#2274" class="Field">base</a>    <a id="2497" class="Symbol">=</a> <a id="2499" href="Causality.Data.Graph.html#2075" class="Function">DirectedGraph.filter-edges</a> <a id="2526" href="Causality.Data.Graph.html#2274" class="Field">base</a> <a id="2531" href="Causality.Data.Graph.html#2472" class="Bound">f</a>
    <a id="2537" class="Symbol">;</a> <a id="2539" href="Causality.Data.Graph.html#2365" class="Field">acyclic</a> <a id="2547" class="Symbol">=</a> <a id="2549" href="Causality.Data.Graph.html#2578" class="Function">acyclic′</a>
    <a id="2562" class="Symbol">}</a>
    <a id="2568" class="Keyword">where</a>
    <a id="2578" href="Causality.Data.Graph.html#2578" class="Function">acyclic′</a> <a id="2587" class="Symbol">:</a> <a id="2589" class="Symbol">_</a>
    <a id="2595" href="Causality.Data.Graph.html#2578" class="Function">acyclic′</a> <a id="2604" class="Symbol">(</a><a id="2605" href="Causality.Data.Graph.html#2605" class="Bound">p</a> <a id="2607" href="Agda.Builtin.Sigma.html#218" class="InductiveConstructor Operator">,</a> <a id="2609" href="Causality.Data.Graph.html#2609" class="Bound">linked</a><a id="2615" class="Symbol">)</a> <a id="2617" class="Symbol">=</a> <a id="2619" href="Causality.Data.Graph.html#2365" class="Field">acyclic</a> <a id="2627" class="Symbol">(</a><a id="2628" href="Causality.Data.Graph.html#2605" class="Bound">p</a> <a id="2630" href="Agda.Builtin.Sigma.html#218" class="InductiveConstructor Operator">,</a> <a id="2632" href="Causality.Data.Graph.html#1614" class="Function">filter-edges-removes-paths</a> <a id="2659" href="Causality.Data.Graph.html#2609" class="Bound">linked</a><a id="2665" class="Symbol">)</a>
</pre>