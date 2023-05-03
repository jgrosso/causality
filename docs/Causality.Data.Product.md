---
title: Causality.Data.Product
---

Definitions and proofs about dependent products.

<pre class="Agda"><a id="98" class="Symbol">{-#</a> <a id="102" class="Keyword">OPTIONS</a> <a id="110" class="Pragma">--without-K</a> <a id="122" class="Pragma">--safe</a> <a id="129" class="Symbol">#-}</a>

<a id="134" class="Keyword">module</a> <a id="141" href="Causality.Data.Product.html" class="Module">Causality.Data.Product</a> <a id="164" class="Keyword">where</a>

<a id="171" class="Keyword">open</a> <a id="176" class="Keyword">import</a> <a id="183" href="Data.Product.html" class="Module">Data.Product</a> <a id="196" class="Keyword">using</a> <a id="202" class="Symbol">(</a><a id="203" href="Data.Product.html#1094" class="Function">∃-syntax</a><a id="211" class="Symbol">;</a> <a id="213" href="Data.Product.html#771" class="Function">∃₂</a><a id="215" class="Symbol">;</a> <a id="217" href="Data.Product.Base.html#1118" class="Function Operator">_×_</a><a id="220" class="Symbol">;</a> <a id="222" href="Agda.Builtin.Sigma.html#218" class="InductiveConstructor Operator">_,_</a><a id="225" class="Symbol">)</a>
<a id="227" class="Keyword">open</a> <a id="232" class="Keyword">import</a> <a id="239" href="Level.html" class="Module">Level</a> <a id="245" class="Keyword">using</a> <a id="251" class="Symbol">(</a><a id="252" href="Agda.Primitive.html#591" class="Postulate">Level</a><a id="257" class="Symbol">)</a>
<a id="259" class="Keyword">open</a> <a id="264" class="Keyword">import</a> <a id="271" href="Relation.Nullary.html" class="Module">Relation.Nullary</a> <a id="288" class="Keyword">using</a> <a id="294" class="Symbol">(</a><a id="295" href="Relation.Nullary.Decidable.Core.html#2264" class="Function Operator">_×-dec_</a><a id="302" class="Symbol">)</a>
<a id="304" class="Keyword">open</a> <a id="309" class="Keyword">import</a> <a id="316" href="Relation.Unary.html" class="Module">Relation.Unary</a> <a id="331" class="Keyword">using</a> <a id="337" class="Symbol">(</a><a id="338" href="Relation.Unary.html#3694" class="Function">Decidable</a><a id="347" class="Symbol">)</a>

<a id="350" class="Keyword">private</a>
  <a id="360" class="Keyword">variable</a>
    <a id="373" href="Causality.Data.Product.html#373" class="Generalizable">a</a> <a id="375" href="Causality.Data.Product.html#375" class="Generalizable">a′</a> <a id="378" href="Causality.Data.Product.html#378" class="Generalizable">b</a> <a id="380" href="Causality.Data.Product.html#380" class="Generalizable">b′</a> <a id="383" href="Causality.Data.Product.html#383" class="Generalizable">c</a> <a id="385" class="Symbol">:</a> <a id="387" href="Agda.Primitive.html#591" class="Postulate">Level</a>
    <a id="397" href="Causality.Data.Product.html#397" class="Generalizable">A</a>           <a id="409" class="Symbol">:</a> <a id="411" href="Agda.Primitive.html#320" class="Primitive">Set</a> <a id="415" href="Causality.Data.Product.html#373" class="Generalizable">a</a>
    <a id="421" href="Causality.Data.Product.html#421" class="Generalizable">A′</a>          <a id="433" class="Symbol">:</a> <a id="435" href="Agda.Primitive.html#320" class="Primitive">Set</a> <a id="439" href="Causality.Data.Product.html#375" class="Generalizable">a′</a>
    <a id="446" href="Causality.Data.Product.html#446" class="Generalizable">B</a>           <a id="458" class="Symbol">:</a> <a id="460" href="Causality.Data.Product.html#397" class="Generalizable">A</a>       <a id="468" class="Symbol">→</a> <a id="470" href="Agda.Primitive.html#320" class="Primitive">Set</a> <a id="474" href="Causality.Data.Product.html#378" class="Generalizable">b</a>
    <a id="480" href="Causality.Data.Product.html#480" class="Generalizable">B′</a>          <a id="492" class="Symbol">:</a> <a id="494" href="Causality.Data.Product.html#397" class="Generalizable">A</a>       <a id="502" class="Symbol">→</a> <a id="504" href="Agda.Primitive.html#320" class="Primitive">Set</a> <a id="508" href="Causality.Data.Product.html#380" class="Generalizable">b′</a>
    <a id="515" href="Causality.Data.Product.html#515" class="Generalizable">C</a>           <a id="527" class="Symbol">:</a> <a id="529" class="Symbol">(</a><a id="530" href="Causality.Data.Product.html#530" class="Bound">x</a> <a id="532" class="Symbol">:</a> <a id="534" href="Causality.Data.Product.html#397" class="Generalizable">A</a><a id="535" class="Symbol">)</a> <a id="537" class="Symbol">→</a> <a id="539" href="Causality.Data.Product.html#446" class="Generalizable">B</a> <a id="541" href="Causality.Data.Product.html#530" class="Bound">x</a> <a id="543" class="Symbol">→</a> <a id="545" href="Agda.Primitive.html#320" class="Primitive">Set</a> <a id="549" href="Causality.Data.Product.html#383" class="Generalizable">c</a>
</pre>
Haskell's fanout function on arrows, `(&&&)`, specialized to `→`.

<pre class="Agda"><a id="_&amp;&amp;&amp;_"></a><a id="631" href="Causality.Data.Product.html#631" class="Function Operator">_&amp;&amp;&amp;_</a> <a id="637" class="Symbol">:</a> <a id="639" class="Symbol">((</a><a id="641" href="Causality.Data.Product.html#641" class="Bound">x</a> <a id="643" class="Symbol">:</a> <a id="645" href="Causality.Data.Product.html#397" class="Generalizable">A</a><a id="646" class="Symbol">)</a> <a id="648" class="Symbol">→</a> <a id="650" href="Causality.Data.Product.html#446" class="Generalizable">B</a> <a id="652" href="Causality.Data.Product.html#641" class="Bound">x</a><a id="653" class="Symbol">)</a> <a id="655" class="Symbol">→</a> <a id="657" class="Symbol">((</a><a id="659" href="Causality.Data.Product.html#659" class="Bound">x</a> <a id="661" class="Symbol">:</a> <a id="663" href="Causality.Data.Product.html#397" class="Generalizable">A</a><a id="664" class="Symbol">)</a> <a id="666" class="Symbol">→</a> <a id="668" href="Causality.Data.Product.html#480" class="Generalizable">B′</a> <a id="671" href="Causality.Data.Product.html#659" class="Bound">x</a><a id="672" class="Symbol">)</a> <a id="674" class="Symbol">→</a> <a id="676" class="Symbol">((</a><a id="678" href="Causality.Data.Product.html#678" class="Bound">x</a> <a id="680" class="Symbol">:</a> <a id="682" href="Causality.Data.Product.html#397" class="Generalizable">A</a><a id="683" class="Symbol">)</a> <a id="685" class="Symbol">→</a> <a id="687" href="Causality.Data.Product.html#446" class="Generalizable">B</a> <a id="689" href="Causality.Data.Product.html#678" class="Bound">x</a> <a id="691" href="Data.Product.Base.html#1118" class="Function Operator">×</a> <a id="693" href="Causality.Data.Product.html#480" class="Generalizable">B′</a> <a id="696" href="Causality.Data.Product.html#678" class="Bound">x</a><a id="697" class="Symbol">)</a>
<a id="699" href="Causality.Data.Product.html#699" class="Bound">f</a> <a id="701" href="Causality.Data.Product.html#631" class="Function Operator">&amp;&amp;&amp;</a> <a id="705" href="Causality.Data.Product.html#705" class="Bound">g</a> <a id="707" class="Symbol">=</a> <a id="709" class="Symbol">λ</a> <a id="711" href="Causality.Data.Product.html#711" class="Bound">x</a> <a id="713" class="Symbol">→</a> <a id="715" href="Causality.Data.Product.html#699" class="Bound">f</a> <a id="717" href="Causality.Data.Product.html#711" class="Bound">x</a> <a id="719" href="Agda.Builtin.Sigma.html#218" class="InductiveConstructor Operator">,</a> <a id="721" href="Causality.Data.Product.html#705" class="Bound">g</a> <a id="723" href="Causality.Data.Product.html#711" class="Bound">x</a>
</pre>
The analogous type-level operator, i.e. with `×` instead of `,`.

<pre class="Agda"><a id="_-×-_"></a><a id="804" href="Causality.Data.Product.html#804" class="Function Operator">_-×-_</a> <a id="810" class="Symbol">:</a> <a id="812" class="Symbol">(</a><a id="813" href="Causality.Data.Product.html#397" class="Generalizable">A</a> <a id="815" class="Symbol">→</a> <a id="817" href="Agda.Primitive.html#320" class="Primitive">Set</a> <a id="821" href="Causality.Data.Product.html#373" class="Generalizable">a</a><a id="822" class="Symbol">)</a> <a id="824" class="Symbol">→</a> <a id="826" class="Symbol">(</a><a id="827" href="Causality.Data.Product.html#397" class="Generalizable">A</a> <a id="829" class="Symbol">→</a> <a id="831" href="Agda.Primitive.html#320" class="Primitive">Set</a> <a id="835" href="Causality.Data.Product.html#378" class="Generalizable">b</a><a id="836" class="Symbol">)</a> <a id="838" class="Symbol">→</a> <a id="840" class="Symbol">(</a><a id="841" href="Causality.Data.Product.html#397" class="Generalizable">A</a> <a id="843" class="Symbol">→</a> <a id="845" href="Agda.Primitive.html#320" class="Primitive">Set</a> <a id="849" class="Symbol">_)</a>
<a id="852" href="Causality.Data.Product.html#852" class="Bound">P</a> <a id="854" href="Causality.Data.Product.html#804" class="Function Operator">-×-</a> <a id="858" href="Causality.Data.Product.html#858" class="Bound">Q</a> <a id="860" class="Symbol">=</a> <a id="862" class="Symbol">λ</a> <a id="864" href="Causality.Data.Product.html#864" class="Bound">x</a> <a id="866" class="Symbol">→</a> <a id="868" href="Causality.Data.Product.html#852" class="Bound">P</a> <a id="870" href="Causality.Data.Product.html#864" class="Bound">x</a> <a id="872" href="Data.Product.Base.html#1118" class="Function Operator">×</a> <a id="874" href="Causality.Data.Product.html#858" class="Bound">Q</a> <a id="876" href="Causality.Data.Product.html#864" class="Bound">x</a>

<a id="_-×-dec-_"></a><a id="879" href="Causality.Data.Product.html#879" class="Function Operator">_-×-dec-_</a> <a id="889" class="Symbol">:</a> <a id="891" class="Symbol">{</a><a id="892" href="Causality.Data.Product.html#892" class="Bound">P</a> <a id="894" class="Symbol">:</a> <a id="896" href="Causality.Data.Product.html#397" class="Generalizable">A</a> <a id="898" class="Symbol">→</a> <a id="900" href="Agda.Primitive.html#320" class="Primitive">Set</a> <a id="904" href="Causality.Data.Product.html#373" class="Generalizable">a</a><a id="905" class="Symbol">}</a> <a id="907" class="Symbol">{</a><a id="908" href="Causality.Data.Product.html#908" class="Bound">Q</a> <a id="910" class="Symbol">:</a> <a id="912" href="Causality.Data.Product.html#397" class="Generalizable">A</a> <a id="914" class="Symbol">→</a> <a id="916" href="Agda.Primitive.html#320" class="Primitive">Set</a> <a id="920" href="Causality.Data.Product.html#378" class="Generalizable">b</a><a id="921" class="Symbol">}</a> <a id="923" class="Symbol">(</a><a id="924" href="Causality.Data.Product.html#924" class="Bound">P?</a> <a id="927" class="Symbol">:</a> <a id="929" href="Relation.Unary.html#3694" class="Function">Decidable</a> <a id="939" href="Causality.Data.Product.html#892" class="Bound">P</a><a id="940" class="Symbol">)</a> <a id="942" class="Symbol">(</a><a id="943" href="Causality.Data.Product.html#943" class="Bound">Q?</a> <a id="946" class="Symbol">:</a> <a id="948" href="Relation.Unary.html#3694" class="Function">Decidable</a> <a id="958" href="Causality.Data.Product.html#908" class="Bound">Q</a><a id="959" class="Symbol">)</a>
  <a id="963" class="Symbol">→</a> <a id="965" href="Relation.Unary.html#3694" class="Function">Decidable</a> <a id="975" class="Symbol">(</a><a id="976" href="Causality.Data.Product.html#892" class="Bound">P</a> <a id="978" href="Causality.Data.Product.html#804" class="Function Operator">-×-</a> <a id="982" href="Causality.Data.Product.html#908" class="Bound">Q</a><a id="983" class="Symbol">)</a>
<a id="985" href="Causality.Data.Product.html#985" class="Bound">P</a> <a id="987" href="Causality.Data.Product.html#879" class="Function Operator">-×-dec-</a> <a id="995" href="Causality.Data.Product.html#995" class="Bound">Q</a> <a id="997" class="Symbol">=</a> <a id="999" class="Symbol">λ</a> <a id="1001" href="Causality.Data.Product.html#1001" class="Bound">x</a> <a id="1003" class="Symbol">→</a> <a id="1005" href="Causality.Data.Product.html#985" class="Bound">P</a> <a id="1007" href="Causality.Data.Product.html#1001" class="Bound">x</a> <a id="1009" href="Relation.Nullary.Decidable.Core.html#2264" class="Function Operator">×-dec</a> <a id="1015" href="Causality.Data.Product.html#995" class="Bound">Q</a> <a id="1017" href="Causality.Data.Product.html#1001" class="Bound">x</a>
</pre>
<pre class="Agda"><a id="1032" class="Keyword">infix</a> <a id="1038" class="Number">2</a> <a id="1040" href="Causality.Data.Product.html#1051" class="Function">∃₂-syntax</a>

<a id="∃₂-syntax"></a><a id="1051" href="Causality.Data.Product.html#1051" class="Function">∃₂-syntax</a> <a id="1061" class="Symbol">=</a> <a id="1063" href="Data.Product.html#771" class="Function">∃₂</a>

<a id="1067" class="Keyword">syntax</a> <a id="1074" href="Causality.Data.Product.html#1051" class="Function">∃₂-syntax</a> <a id="1084" class="Symbol">(λ</a> <a id="1087" class="Bound">x</a> <a id="1089" class="Bound">y</a> <a id="1091" class="Symbol">→</a> <a id="1093" class="Bound">B</a><a id="1094" class="Symbol">)</a> <a id="1096" class="Symbol">=</a> <a id="1098" class="Function">∃[</a> <a id="1101" class="Bound">x</a> <a id="1103" class="Bound">y</a> <a id="1105" class="Function">]</a> <a id="1107" class="Bound">B</a>

<a id="∃₃"></a><a id="1110" href="Causality.Data.Product.html#1110" class="Function">∃₃</a> <a id="1113" class="Symbol">:</a> <a id="1115" class="Symbol">∀</a> <a id="1117" class="Symbol">{</a><a id="1118" href="Causality.Data.Product.html#1118" class="Bound">d</a><a id="1119" class="Symbol">}</a> <a id="1121" class="Symbol">(</a><a id="1122" href="Causality.Data.Product.html#1122" class="Bound">D</a> <a id="1124" class="Symbol">:</a> <a id="1126" class="Symbol">(</a><a id="1127" href="Causality.Data.Product.html#1127" class="Bound">x</a> <a id="1129" class="Symbol">:</a> <a id="1131" href="Causality.Data.Product.html#397" class="Generalizable">A</a><a id="1132" class="Symbol">)</a> <a id="1134" class="Symbol">→</a> <a id="1136" class="Symbol">(</a><a id="1137" href="Causality.Data.Product.html#1137" class="Bound">y</a> <a id="1139" class="Symbol">:</a> <a id="1141" href="Causality.Data.Product.html#446" class="Generalizable">B</a> <a id="1143" href="Causality.Data.Product.html#1127" class="Bound">x</a><a id="1144" class="Symbol">)</a> <a id="1146" class="Symbol">→</a> <a id="1148" href="Causality.Data.Product.html#515" class="Generalizable">C</a> <a id="1150" href="Causality.Data.Product.html#1127" class="Bound">x</a> <a id="1152" href="Causality.Data.Product.html#1137" class="Bound">y</a> <a id="1154" class="Symbol">→</a> <a id="1156" href="Agda.Primitive.html#320" class="Primitive">Set</a> <a id="1160" href="Causality.Data.Product.html#1118" class="Bound">d</a><a id="1161" class="Symbol">)</a> <a id="1163" class="Symbol">→</a> <a id="1165" href="Agda.Primitive.html#320" class="Primitive">Set</a> <a id="1169" class="Symbol">_</a>
<a id="1171" href="Causality.Data.Product.html#1110" class="Function">∃₃</a> <a id="1174" href="Causality.Data.Product.html#1174" class="Bound">D</a> <a id="1176" class="Symbol">=</a> <a id="1178" href="Data.Product.html#1094" class="Function">∃[</a> <a id="1181" href="Causality.Data.Product.html#1181" class="Bound">a</a> <a id="1183" href="Data.Product.html#1094" class="Function">]</a> <a id="1185" href="Data.Product.html#1094" class="Function">∃[</a> <a id="1188" href="Causality.Data.Product.html#1188" class="Bound">b</a> <a id="1190" href="Data.Product.html#1094" class="Function">]</a> <a id="1192" href="Data.Product.html#1094" class="Function">∃[</a> <a id="1195" href="Causality.Data.Product.html#1195" class="Bound">c</a> <a id="1197" href="Data.Product.html#1094" class="Function">]</a> <a id="1199" href="Causality.Data.Product.html#1174" class="Bound">D</a> <a id="1201" href="Causality.Data.Product.html#1181" class="Bound">a</a> <a id="1203" href="Causality.Data.Product.html#1188" class="Bound">b</a> <a id="1205" href="Causality.Data.Product.html#1195" class="Bound">c</a>

<a id="1208" class="Keyword">infix</a> <a id="1214" class="Number">2</a> <a id="1216" href="Causality.Data.Product.html#1227" class="Function">∃₃-syntax</a>

<a id="∃₃-syntax"></a><a id="1227" href="Causality.Data.Product.html#1227" class="Function">∃₃-syntax</a> <a id="1237" class="Symbol">=</a> <a id="1239" href="Causality.Data.Product.html#1110" class="Function">∃₃</a>

<a id="1243" class="Keyword">syntax</a> <a id="1250" href="Causality.Data.Product.html#1227" class="Function">∃₃-syntax</a> <a id="1260" class="Symbol">(λ</a> <a id="1263" class="Bound">x</a> <a id="1265" class="Bound">y</a> <a id="1267" class="Bound">z</a> <a id="1269" class="Symbol">→</a> <a id="1271" class="Bound">C</a><a id="1272" class="Symbol">)</a> <a id="1274" class="Symbol">=</a> <a id="1276" class="Function">∃[</a> <a id="1279" class="Bound">x</a> <a id="1281" class="Bound">y</a> <a id="1283" class="Bound">z</a> <a id="1285" class="Function">]</a> <a id="1287" class="Bound">C</a>
</pre>