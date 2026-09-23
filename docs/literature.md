# Literature search: the Favard-length decay exponent of the four-corner Cantor set

Prepared 2026-09-23 for the Palomar metadata of this repository. Three independent searches (A: citation graph; B: web, blogs, talks and code; C: surveys and the exponent chronology) were run by Claude Code agents, followed by a verification pass (D) that re-fetched every decisive source and ran the searches the others missed. Every query is listed in §4. This account covers `α_Fav := sup{a ≥ 0 : ∃C, Fav(K_n) ≤ C n^{-a} ∀n ≥ 1}`, where `K_n = C_n × C_n` and `C_n` is the depth-n middle-half Cantor approximant (digits {0,3} in base 4). This is constant C_60 / 60a in the teorth optimization-constants registry.

## 1. Primary sources, re-fetched and checked

Each source was downloaded fresh and read with `pdftotext`, `pdftotext -layout` and `grep`.

| Source | What it states (confirmed) | Set it applies to |
|---|---|---|
| **Nazarov–Peres–Volberg**, arXiv:0801.2942 (only v1, 18 Jan 2008). Published in Algebra i Analiz 22(1) (2010) 82–97 = St. Petersburg Math. J. 22 (2011) 61–72, DOI 10.1090/S1061-0022-2010-01133-6. | **Theorem 1** (p. 3): for every δ > 0 there is C > 0 with Fav(K_n) ≤ C n^{δ−1/6} for all n ∈ ℕ. The remarks after it say 1/6 "is certainly not optimal" and "can be improved slightly" with the paper's methods, and that "a bound decaying faster than O(n^{-1/4}) would require new ideas." They also say it is unclear whether Fav(K_n) decays like n^{-1}. **NPV never claim 1/4.** | K_n, the four-corner approximants |
| **Bateman–Volberg**, arXiv:0807.2953; Math. Res. Lett. 17(5) (2010) 959–967 | **Theorem 1, eq. (1.2)**: there is c > 0 with Fav(K_n) ≥ c·log n / n for all n. This gives α_Fav ≤ 1. | K_n |
| **Marshall, arXiv:2509.02882v2** (arXiv stamp 12 Aug 2026; PDF "Date: July 2026"; title *Improved Power Laws for the Favard Length Problem in All Dimensions*; preprint, not refereed) | **Theorem 1.2** (p. 2), restated as **Theorem 8.3** "(The four-corner Cantor set)", eq. (8.14), p. 85: for every u > 0 there are C_u, N_u with Fav(N_{4^{-N}}(K_2^∞)) ≤ C_u N^{-1/5+u} for N ≥ N_u. The proof (pp. 85–86) actually shows Fav(K_2^M) ≲ M^{-1/p} for every p > 5. Remark 2.4, eq. (2.2), gives Fav(N_{L^{-N}}(S^∞)) ≈_d Fav(S^N), so **α_Fav ≥ 1/5**. | K_n (the four-corner set) |
| Marshall v2, §8.5, p. 84 | "the formal substitution D = 1 (which would yield a final exponent of 1/4 − u) in (8.7) is not justified by our current methods." | four-corner |
| Marshall v2, p. 86 | "Anything beyond this 1/5 barrier would require either a significant reworking of the combinatorial arguments in Section 7, or else another perspective replacing the current Fourier analytic arguments…" | four-corner |
| Marshall v2, Future Directions, around (8.27), pp. 93–94 | A weighted estimate saving one power of K over the pointwise NPV lower bound would have analytic cost λ = 3 and would give 1/4 − u. A full weighted estimate (λ = 2) would give 1/3 − u. Marshall calls these "conditional applications of (8.27); neither weighted input is used in the proved theorems … currently unavailable to us." | four-corner |
| Marshall v2, p. 7 (§2.1) | Gives 1/3 − u for the base-25 digit set {0,1,2,6,9}², and δ₃₆ ≈ 0.3407 for a base-36 example. It says these "concern different digit sets and do not assert the corresponding improvement for the four-corner Cantor set." | other sets only |
| **Marshall, arXiv:2509.02882v1** (2 Sep 2025; title *Power Laws for the Favard Length Problem in R^d*; superseded) | **Remark 1.3** (p. 3): the characterization "also strengthens the bound of Nazarov, Peres, and Volberg to ϵ > 1/4 (which was known in [27] but not explicitly proven)". **§3.5, after the proof of Proposition 3.20** (pp. 25–26): "for any u ∈ (1/4, ∞] … Fav(N_{4^{-N}}(K^∞)) ≲ N^{-δ(1,0)} = N^{-1/4+u}", with the added claim that this "recovers the best possible power law decay for the four-corner set." The quantifier is garbled, the digit set is misprinted as {1,3}, and the sign of u is wrong: the argument would at best give 1/4 − u. | four-corner (claim later withdrawn) |
| **teorth/optimizationproblems, constants/60a.md** | The current file at main commit `9d57db86` (2026-09-05) says "The best established range currently is 1/6 ≤ α_Fav ≤ 1". Lower bound cited to NPV2011, upper bound to BV2010. The file has one commit ever (`a0bc982`, 2026-02-21). README row 60 reads 1/6 and 1. There are 0 issues or PRs matching "Favard". None of the open PRs, up to #194 (2026-09-21), touches 60a. Marshall's 1/5 is **not** recorded. The registry's definition matches the one formalized (sup over "for all n ∈ ℕ"). | K_n |
| **Łaba–McDonald–Taylor**, arXiv:2607.28793 (30 Jul 2026) | Eq. (2.9): Fav(K_n) ≲_ε n^{-1/6+ε} for all ε > 0 [NPV], "see also [3]" (Bond's thesis). The most recent expert statement found still gives 1/6. | K_n |
| **Pith machine review** of 2509.02882 (pith.science/paper/2509.02882) | It reviews v1 and notes that v2 is newer. Dated 2026-08-05, model deepseek-v4-flash. It flags the N^{-1/4+u} bound as a sign error (it should be 1/4 − u). It also flags a factor-2 error in α and an ε₀ inequality-direction error in the main proof, which make the Proposition 3.20 exponent claims "unsupported as written". This is not a human referee report. | four-corner |

Discrepancies between the verification pass and the three reports:
- None on substance. All three agree with the primary texts on theorem numbers, exponents and sets.
- The v1 digit-set typo ({1,3} instead of {0,3}, p. 25) is new.
- `pdftotext` renders the stacked fractions as "16" and "41". The rendered-page checks in reports A and B confirm these read 1/6 and 1/4.


## 2. History of the upper-bound exponent (bounds on Fav(K_n) from above, i.e. lower bounds on α_Fav)

1. **Besicovitch (1939)**, qualitative: Fav(K) = 0, so Fav(K_n) → 0 with no rate.
2. **Peres–Solomyak**, Pacific J. Math. 204(2) (2002) 473–496, DOI 10.2140/pjm.2002.204.473, Thm 1.1: Fav(K_n) ≤ C exp(−a log* n). This is the first explicit rate. Their Thm 2.2 gives E[Fav] ~ 1/n for random four-corner sets. (Report C read this.)
3. **Tao**, arXiv:0706.2646; Proc. LMS 98 (2009) 559–584, Prop. 1.21: Fav(K_n) ≲ (log* n)^{-1/100}. The method is general but the bound is weaker.
4. **Nazarov–Peres–Volberg**, arXiv Jan 2008; journal 2010/2011, Thm 1: **α_Fav ≥ 1/6**. This is the first power law and the best peer-reviewed bound. It is also the "1/4 needs new ideas" remark.
5. Extensions with no gain for K:
   - Łaba–Zhai, Bull. LMS 42 (2010), arXiv:0902.0964;
   - Bond–Volberg, gasket and general self-similar sets, 2009–2012, arXiv:0911.0233, 0912.5111, 0905.0207, 0912.5095, 0811.1302;
   - Bond–Łaba–Volberg, Amer. J. Math. 136 (2014), arXiv:1109.1031;
   - Bond, PhD thesis, MSU 2011;
   - Łaba–Marshall, Discrete Analysis 2022, arXiv:2202.07555.

   All of them quote 1/6, or something weaker, for K.
6. Surveys and papers restating 1/6 as the four-corner record:
   - Łaba survey (arXiv:1212.0247; Abel Symp. 2015);
   - Bishop–Peres (2017);
   - Cladek–Davey–Taylor (IUMJ 2022);
   - Vardakis–Volberg (JMAA 2024);
   - Dąbrowski (arXiv:2408.03919, 2024);
   - Chang–Shmerkin–Suomala (GAFA 36 (2026));
   - Łaba–McDonald–Taylor (Jul 2026);
   - the teorth registry, 60a (Feb 2026, still current).
7. **Marshall arXiv:2509.02882v1 (2 Sep 2025)** claimed N^{-1/4+u} (should read 1/4 − u) and attributed it to NPV as "known but not explicitly proven". That misreads NPV's remark. The claim is unsupported, and v2 withdrew it.
8. **Marshall arXiv:2509.02882v2 (12 Aug 2026)** proves **α_Fav ≥ 1/5**. NPV's Fourier input is kept, and the K^{2+o(1)} propagation is replaced by K^{1+o(1)}. The author calls 1/5 a barrier for his methods and names the missing weighted low-frequency input that would give 1/4 − u. This is an unrefereed preprint.

Bounds from below on Fav(K_n) (these cap α_Fav):
- Mattila, IUMJ 39 (1990) 185–198, Thm 4.1: Fav(K_n) ≳ 1/n.
- Bongers, PAMS 147 (2019), Cor. 3.2: an elementary proof of ≳ 1/n.
- **Bateman–Volberg**, MRL 17 (2010), Thm 1: ≥ c log n / n. So **α_Fav ≤ 1**.
- Bongers, arXiv:2605.05098 (2026): energy methods cannot beat 1/n.

The consensus conjecture is α_Fav = 1: Peres–Solomyak, Tao, Łaba, Dąbrowski.

**Best bound on record before this work:**
- Peer-reviewed, and the registry value: **1/6** (NPV).
- Best claimed anywhere: **1/5** (Marshall v2, preprint, Aug 2026). The registry has not recorded it yet.

## 3. Does anything at or beyond 1/4 exist for this set?

- **Claims:** there is exactly one independent claim, **Marshall v1 (Sep 2025)**, Remark 1.3 and §3.5. The author withdrew it in v2 as "not justified by our current methods". A machine review (Pith, Aug 2026) also flagged it as unsupported. The only other ≥ 1/4 claim found is this project's own public repository, github.com/CoolRmal/FavardLength (the origin remote, created 2026-09-23), which is already indexed by web search. It is not independent.
- **Proofs:** none. No paper, preprint, thesis abstract, survey, registry entry, blog post, MathOverflow post, talk abstract or code repository contains a proof of α_Fav ≥ 1/4, or of Fav(K_n) ≲ n^{-1/4+ε}, for the four-corner set.
- Exponents ≥ 1/4 appear only for **other** digit sets: Marshall v2's 1/3 − u (base 25) and δ₃₆ ≈ 0.3407 (base 36). Marshall explicitly says these do not transfer to the four-corner set.
- **Context for novelty:**
  - The target 1/4 is anticipated in print. NPV's "new ideas" remark names it.
  - The reduction route is also anticipated. Marshall v2 (pp. 93–94) calls a weighted estimate saving one power of K "conditional … currently unavailable".
  - The repo manuscript (`references/favard-optimized-quarter-proof.md`) says it adds a joint negative-moment estimate for the entire low-frequency product. That is exactly the input Marshall calls missing.
  - So the metadata should present the work as **the first proof, and the first machine-checked proof, of the step Marshall v2 identifies as missing**. It should cite NPV's remark, Marshall v2 §8.5 and (8.27), and the withdrawn v1 claim.
  - Reviewers will likely probe whether the negative-moment step really delivers the one-power-of-K saving. The Lean kernel check answers this for the formal statement, provided the Lean definitions of C_n, K_n and Fav match the registry's (they appear to).
  - The Lean result proves sup ≥ 1/4. It does not show that a = 1/4 itself is admissible. This is consistent with NPV's barrier being stated as "faster than O(n^{-1/4})".

## 4. Queries run, grouped by tool, with outcomes

Queries are reproduced from the three reports (A, B, C) plus my own verification pass (D). Report C gave its arXiv API queries in URL form. The Crossref/OpenAlex lines C only summarized are listed as C gave them.

### arXiv (PDF/abs/HTML fetches, `curl` + `pdftotext`)
- A: `curl -L https://arxiv.org/pdf/2509.02882v1 + pdftotext + pdftoppm pages 2,3,25` → 1/4 claim on p.25 and Remark 1.3
- A: `curl -L https://arxiv.org/pdf/2509.02882v2 + pdftotext` → Thm 1.2/8.3 is 1/5; 1/4 not justified / conditional
- A: `curl -L https://arxiv.org/abs/2509.02882` → v1 2 Sep 2025, v2 12 Aug 2026; `curl -L https://arxiv.org/abs/2509.02882v1` → 51 pages
- A: `curl -L https://arxiv.org/pdf/0801.2942 + pdftotext` → Thm 1 is 1/6; remark on the 1/4 barrier
- A: `curl -L https://arxiv.org/pdf/{2607.28793,2605.05098,2512.17753v1,2512.17753v2,2609.04684,2609.24623,2609.08568,2609.03400} + pdftotext + grep` → no four-corner exponent above 1/6; LMT (2.9) = 1/6
- A: `curl -L https://arxiv.org/pdf/{2602.22002,2608.10253,2608.10476,2606.00381,2608.28770,2605.27550,2606.10608} + pdftotext + grep` → no four-corner exponent claims
- A: `curl -L https://arxiv.org/pdf/{1212.0247,0902.0964,1109.1031,2202.07555,2003.03620,0807.2953,2507.11672,0706.2646v2} + pdftotext + grep` → key statements read
- B: `WebFetch https://arxiv.org/abs/2509.02882`; `curl -A Mozilla https://arxiv.org/abs/2509.02882` → v1 49KB, v2 339KB, no v3
- B: `curl https://arxiv.org/pdf/2509.02882v1 + pdftotext + pdftoppm pp.3,25` → 1/4 claim confirmed; `curl https://arxiv.org/pdf/2509.02882v2 + pdftotext` → 1/5; 1/4 disowned pp.84, 93–94; `curl https://arxiv.org/pdf/0801.2942 + pdftotext`
- B: `curl+pdftotext arXiv PDFs 2607.28793, 2605.05098, 2512.17753, 2609.08568, 2609.04684, 2609.24623, 2408.03919, 2507.11672, 2608.10253, 2606.00381, 2608.10476, 2609.03400, 1212.0247, 2602.22002, 2003.03620` → none claims ≥ 1/4
- C: `curl https://arxiv.org/pdf/{0801.2942,0807.2953,2509.02882v2,2509.02882v1,0902.0964,1212.0247,2003.03620,2512.17753,0911.0233,0912.5111,1205.2899,1801.06904} + pdftotext` → read
- C: `curl https://arxiv.org/pdf/{2607.28793,2605.05098,2609.04684,1109.1031,2202.07555,2507.11672,2408.03919,1711.09858,1707.08137,2205.14559,0811.1302,0905.0207,0912.5095,2105.01708,2104.00826,2203.01279} + pdftotext` → scanned for four-corner statements
- C: `curl https://arxiv.org/pdf/0706.2446` → wrong ID copied from NPV's reference list (an astro-ph paper); `curl https://arxiv.org/pdf/0706.2646` → Tao v2
- C: `curl https://arxiv.org/pdf/2112.00540` → Mattila survey, no rate; `curl https://arxiv.org/pdf/2608.10253`, `…/2606.00381` → no exponent
- C: `curl https://arxiv.org/abs/2509.02882` → only v1 and v2; `curl https://arxiv.org/html/2509.02882v1`, `…/html/2509.02882v2` → HTML numbering differs (HTML Thm 8.2 = PDF 8.3; HTML Prop 3.5 = PDF 3.20)
- C: `curl https://arxiv.org/abs/{0801.2942,0807.2953,0902.0964,1212.0247,2512.17753,2003.03620}` → NPV and BV have only v1
- D: `curl -sL https://arxiv.org/pdf/{2509.02882v1,2509.02882v2,0801.2942,0807.2953} + pdftotext [-layout]` → all statements in §1 re-confirmed verbatim
- D: `curl -sL https://arxiv.org/pdf/2607.28793 + grep "(2.9)"` → n^{-1/6+ε}, confirmed
- D: `curl -sL https://arxiv.org/pdf/2211.16911v2` (Dąbrowski, PLMS 2025) and `https://arxiv.org/pdf/2606.24461` + grep → no four-corner exponent statement

### arXiv export API (metadata search; arXiv has no full-text search)
- A: `export.arxiv.org/api/query?id_list=2509.02882` → v2 abstract gives N^{-1/5+u}
- A: `search_query=abs:%22Favard%20length%22&max_results=200&sortBy=submittedDate` → 24 results; 2026: 2607.28793, 2605.05098, 2512.17753v2
- A: `search_query=all:%22four-corner%22%20AND%20all:Cantor` → 15 results, incl. 2609.24623, 2609.08568, 2609.04684, 2609.03400
- A: `abs:Buffon` [26]; `abs:%22Garnett%20set%22` [0]; `ti:Favard` [23]; `abs:%22four%20corner%20Cantor%22` [10]; `abs:%22product%20Cantor%22` [7]; `abs:%22Besicovitch%20projection%22` [6]; `abs:Buffon%20AND%20abs:Cantor` [6]; `all:Favard%20AND%20all:Cantor` [17]
- A: `id_list=0807.2953,0902.0964,0911.0233,0912.5095,0912.5111,1109.1031,0706.2646,2105.01708,1711.09858,1212.0247,2003.03620,2202.07555,2507.11672,2408.03919,1707.08137,1801.06904,2211.16911,0811.1302,0905.0207` → abstracts read
- B: `id_list=2509.02882`; `all:"Favard length"` sorted by date [26]; `all:Buffon AND (cat:math.CA OR cat:math.MG)` [15, unrelated]; `all:"four-corner"` [93]; `all:"four corner Cantor"` [14]; `all:"Garnett set"` [0]; `all:"Garnett" AND all:Cantor` [0]; `all:"Favard" AND submittedDate:[202501010000 TO 202609302359]` [14]; `abs:"Favard curve length"` [3]; `abs:"Buffon" AND submittedDate:[…2025–2026]` [4, unrelated]; `abs:"unrectifiable" AND abs:"power law"` [0]; `abs:"projections" AND abs:"four corner"` [15]; `abs:"average projection" AND abs:Cantor AND submittedDate 2025–2026` [0]; `abs:"Besicovitch projection" AND submittedDate 2025–2026` [1: 2606.00381]
- C: `search_query=all:%22four-corner%22+AND+all:Favard` [6]; `all:%22four+corner%22+AND+all:Favard` [6]; `all:Favard+AND+all:Cantor` [17]; `ti:Favard`; `ti:Buffon`; `abs:Favard`; `abs:%22four-corner%22`; `abs:%22Garnett+set%22` [0]; `abs:%22Buffon%22+AND+abs:Cantor`; `au:Mattila+AND+ti:Rectifiability`; `au:Eiderman+AND+au:Volberg` [not on arXiv]; `ti:"quantitative version of the Besicovitch projection theorem"`
- D: `id_list=2509.02882` → v2 updated 2026-08-12, v1 published 2025-09-02, no v3
- D: sorted by submittedDate desc, max 8 each: `all:Favard`; `all:%22four-corner%22`; `all:%22four%20corner%22%20AND%20all:Cantor`; `all:Buffon%20AND%20all:Cantor`; `all:%22Garnett%22%20AND%20all:projection` → newest relevant is 2609.24623 (21 Sep 2026, already checked); nothing new
- D: `search_query=ti:%22Quantitative%20Besicovitch%20projection%20theorem%20for%20irregular%22` → 2211.16911

### OpenAlex
- A: `works?search=power%20law%20Buffon%20needle%20probability%20four-corner%20Cantor%20set` → NPV W2116420039 (23 cites), W2950321433 (9); `filter=cites:W2116420039` [23 citers, none with a claim]; `filter=cites:W2950321433` [9]; `search=Improved%20Power%20Laws…` → W4417409424 (0 cites) and dissertation W7155657543; `works/doi:10.48550/arXiv.2509.02882` [shell error]; `works/W7155657543` → dissertation abstract; `filter=cites:W4417409424` [0]; `search=%22Favard%20length%22&filter=from_publication_date:2025-01-01` [24]; `works/doi:10.46569/5999nd30f` [Hadley, not relevant]; `works/doi:10.2140/pjm.2002.204.473`, `doi:10.1512/iumj.1990.39.39011` [no abstracts]
- B: `works?search="four-corner Cantor" Favard&filter=from_publication_date:2025-01-01` [12]; `works?search="Favard length"&filter=from_publication_date:2025-01-01` [24]; `works/doi:10.14288/1.0452055` [thesis abstract, no exponent]
- D: `works?filter=fulltext.search:%22four-corner%20Cantor%20set%22,from_publication_date:2025-01-01` → **18 full-text hits**, all checked; new to this pass: Dąbrowski PLMS 2025 (2211.16911) and 2606.24461, neither with a four-corner exponent
- D: `works?filter=fulltext.search:%22Favard%20length%22,from_publication_date:2026-01-01` → 18 hits, all previously checked or irrelevant (incl. Marshall dissertation W7155657543 and SIAM 10.1137/25m1804054)
- D: `works?filter=fulltext.search:%22Buffon%20needle%22,from_publication_date:2025-06-01` → "Search temporarily unavailable"; `works?search=Favard%20length%20Cantor&filter=from_publication_date:2026-06-01` → 5, all known
- D: `works/{W7163597891,W7164447459,W7162817784,W7165972933}` → resolved to 2606.00381, 2606.10608, 2605.27550, 2606.24461

### Semantic Scholar
- A: `graph/v1/paper/arXiv:0801.2942?fields=…` [429]; `arXiv:2509.02882?fields=…` [429]; retry loop over `{arXiv:0801.2942,arXiv:2509.02882,DOI:10.1090/S1061-0022-2010-01133-6}/citations` → 42 citing NPV, 0 citing Marshall; `WebFetch …/arXiv:0801.2942/citations` [429]; `arXiv:2509.02882?fields=title,year,citationCount,referenceCount,…` → references not parsed; `paper/search?query=Power+Law+Buffon+Needle+Probability+Four-Corner+Cantor+Set+after` → 2018 Taylor record, no PDF
- B: `…/arXiv:0801.2942/citations` → recent citers 2608.10253, 2607.28793, 2606.00381, 2512.17753; `…/arXiv:2509.02882/citations` [429, then empty]
- C: `…/arXiv:0801.2942/citations`; `…/arXiv:2509.02882/citations` [429, then empty]; `…/arXiv:0807.2953/citations` [nothing new]
- D: `graph/v1/snippet/search?query=Favard length four-corner Cantor set n^{-1/4}`, `…four-corner Cantor set Favard exponent 1/4`, `…Favard length four-corner Cantor set exponent 1/4` → 429 on all 5 attempts (full-text snippet search not reached)

### OpenCitations / Crossref / zbMATH
- A: `opencitations.net/index/coci/api/v1/citations/10.1090/s1061-0022-2010-01133-6` [301]; `api.opencitations.net/index/v2/citations/doi:10.1090/s1061-0022-2010-01133-6` [10]; `…doi:10.48550/arxiv.0801.2942` [0]; `…doi:10.48550/arxiv.2509.02882` [0]
- A: `api.zbmath.org/v1/document/_search?search_string=ti%3Afour-corner`; `…ti%3A%22Buffon%20needle%20probability%22` → NPV Zbl 1213.28006, BV Zbl 1223.28008; `…ci%3A1213.28006` [3]; `…ci%3A5863958` [3]; `rf%3A…`, `cited_by%3A…` [404]; `…ut%3AFavard%20length` [21, none improving 1/6]; `…ti%3AFavard` [244]; `document/5863958` → review confirms n^{δ−1/6}
- A: `api.crossref.org/works?query.bibliographic=…` (Peres–Solomyak; Mattila; Tao; Bongers–Taylor; Circular Favard); `works/{10.1512/iumj.1990.39.39011,10.1007/s00039-026-00743-3,10.1090/s1061-0022-2010-01133-6,10.4310/mrl.2010.v17.n5.a12,10.1112/blms/bdq059,10.1353/ajm.2014.0013,10.1512/iumj.2012.61.4828}`; `works?query.bibliographic=Lower%20bounds%20for%20mask%20polynomials…`
- C: Crossref `works/{10.1007/s12220-010-9141-4, 10.1090/S1061-0022-2010-01133-6, 10.4310/MRL.2010.v17.n5.a12, 10.2140/pjm.2002.204.473, 10.1112/blms/bdq059, 10.1512/iumj.1990.39.39011}`; guessed BLV DOI 10.1353/ajm.2014.0009 [wrong]; bibliographic queries for 7 titles [partly rate-limited]
- D: `api.crossref.org/works/10.1112/plms.70037` → Dąbrowski, Mar 2025

### Google Scholar
- A: `WebFetch scholar.google.com/scholar?cites=0&q=%22power+law+for+the+Buffon…%22` → NPV "Cited by 51"; `WebFetch …?cites=17859061768765410193…` [CAPTCHA]; Browser pane navigate to the same [CAPTCHA, stopped]; `WebFetch …?q=%22Improved+Power+Laws…%22` → found, no cited-by count
- D: `WebFetch https://scholar.google.com/scholar?q=%22Favard+length%22+%22four-corner%22&as_ylo=2026` → 8 results for 2026 (LMT, CSS, Bongers, Hadley, Li–Taylor, BBMT, Iosevich–Li–Palsson–Taylor, Iosevich–Li–Taylor), all already checked, none claiming 1/4
- D: `WebFetch https://scholar.google.com/scholar?q=%22Favard+length%22+%22n%5E%7B-1%2F4%7D%22+OR+%22N%5E%7B-1%2F4%7D%22+Cantor` → 3 results: NPV (the barrier remark only), Marshall 2025, Orponen JEMS 2023. The fetch tool's summarizer called NPV's n^{-1/4} "a current bound"; that is a misreading of the barrier remark. No claim.

### Web search (general)
- A: "four-corner Cantor set Favard length upper bound exponent improved 2026"; "\"four-corner Cantor set\" Favard length \"1/4\" power law"; "Nazarov Peres Volberg \"power law for the Buffon needle probability\" cited by"; "\"Favard length\" four-corner arXiv 2026"; "\"Garnett set\" OR \"Garnett-Ivanov\" Favard length decay rate n^{-1/4}"; "\"The Power Law For The Buffon Needle Probability Of The Four-Corner Cantor Set\" after Nazarov Peres Volberg Krystal Taylor notes"; "\"four-corner\" Cantor \"Favard length\" \"n^{-1/4}\" OR \"N^{-1/4}\" upper bound"; "Caleb Marshall \"The Favard length problem for self-similar sets\" UBC dissertation 2026"; "Buffon needle four-corner Cantor set new bound 2026 preprint Favard decay exponent"; "\"Favard length\" four-corner \"negative moment\" OR \"Riesz product\" low-frequency product improvement exponent"; "site:arxiv.org \"four-corner Cantor set\" Favard 2026". Outcomes: Marshall, the classics, and the CoolRmal repo only.
- B: "\"Favard length\" \"four-corner Cantor set\" improved exponent"; "Favard length four-corner Cantor set n^{-1/4} bound 2026"; "\"Buffon needle\" \"four-corner\" Cantor set power law new bound"; "mathoverflow Favard length four corner Cantor set decay rate"; "site:mathoverflow.net \"Favard length\""; "terrytao.wordpress.com Favard length Buffon needle Cantor set"; "ilaba.wordpress.com Favard length four-corner Cantor set"; "Matthew Bond thesis \"Combinatorial and Fourier analytic L2 methods for Buffon's needle problem\""; "Caleb Marshall Favard length talk seminar 2026 four-corner exponent"; "\"Favard length\" seminar abstract 2026"; "\"Garnett set\" Favard length Buffon needle"; "\"four-corner Cantor set\" Favard \"1/4\" exponent new ideas Nazarov Peres Volberg improvement"; "arxiv 2026 \"Favard length\" Cantor set upper bound exponent"; "\"Buffon's needle\" Cantor set 2026 arXiv math.CA"; "teorth optimizationproblems Favard-length decay exponent"; "\"The Favard length problem for self-similar sets\" Marshall UBC thesis"; "Falconer \"Seventy Years of Fractal Projections\" Favard four-corner"; "\"Favard\" \"four-corner\" \"n^{-1/4}\" OR \"N^{-1/4}\" Cantor"; "Nazarov Peres Volberg exponent 1/6 improved \"1/5\" Favard four corner Marshall"; "\"Favard length\" blog post 2025 OR 2026 Cantor set projections"; "\"7/33\" Favard length four-corner Cantor"; "\"Favard length\" \"four-corner\" Lean formalization OR \"negative moment\" exponent quarter". Outcomes: nothing beyond Marshall and the repo; no source uses 7/33.
- C: "Favard length four-corner Cantor set upper bound exponent"; "Marshall \"Improved Power Laws for the Favard Length Problem in All Dimensions\""; "Buffon needle four-corner Cantor set power law n^{-1/6}"; "Peres Solomyak \"How likely is Buffon's needle to fall near a planar Cantor set\" Pacific Journal of Mathematics 2002"; "Mattila \"Orthogonal projections, Riesz capacities, and Minkowski content\" Indiana University Mathematics Journal 1990"; "Bond Volberg \"Circular Favard length of the four-corner Cantor set\" arXiv"; "Bond Łaba Volberg \"Buffon's needle estimates for rational product Cantor sets\" arXiv"; "Matthew Bond thesis … Michigan State University 2011"; "\"four-corner Cantor set\" Favard length \"n^{-1/4}\" OR \"1/4\" exponent improved bound"; "Favard length four corner Cantor set 2026 new bound exponent"; "Bishop Peres \"Fractals in Probability and Analysis\" four corner Cantor set Favard length Buffon needle chapter"; "Krystal Taylor \"Connections between fractal geometry and projections\" Notices AMS 2024"; "Volberg Eiderman \"Non-homogeneous harmonic analysis: 16 years of development\" Russian Mathematical Surveys 2013 four-corner Favard"; "\"The Power Law For The Buffon Needle Probability Of The Four-Corner Cantor Set\" after Nazarov Peres Volberg notes Taylor 2018"; "mathoverflow Favard length four corner Cantor set rate of decay conjecture 1/n". Outcomes: nothing new.
- D: "\"Favard length\" \"four-corner\" \"n^{-1/4}\" OR \"1/4\" exponent proof 2026"; "Favard length four-corner Cantor set September 2026 arXiv new exponent"; "\"Buffon needle\" \"four-corner Cantor set\" \"negative moment\" OR \"Riesz product\" Favard exponent"; "Marshall \"The Favard length problem for self-similar sets\" dissertation four-corner exponent". Outcomes: only Marshall, the classics, the CoolRmal repo and a Pith page.

### Other web fetches (WebFetch / curl)
- A: `WebFetch https://msp.org/pjm/2002/204-2/p13.xhtml` [404]; `doi.org/10.2140/pjm.2002.204.473` → `msp.org/…/p10.xhtml` [landing page]; `www.mathnet.ru/eng/aa1167` [wrong article]; `www.ams.org/spmj/2011-22-01/…pdf` [HTML]; `github.com/CoolRmal/FavardLength` [the repo; claims 1/4]; `teorth.github.io/optimizationproblems/constants/60a.html` [1/6, 1]; `bondmatt.wordpress.com/2011/03/02/thesis-second-complete-draft/` and `…/thesis-7-0.pdf` [p < 1/6 only]; `sites.google.com/view/calebmarshallmath/home`, `…/writing` [lists dissertation, v2, 2608.10253, 2608.10476]; UBC `open.library.ubc.ca/media/download/pdf/24/1.0452055/3`, `hdl.handle.net/2429/94186`, cIRcle item page, and Browser pane → all blocked, not bypassed
- B: `curl -sL teorth…/60a.html`; `WebFetch terrytao.wordpress.com/2007/06/19/…` [no later updates]; `curl 'https://ilaba.wordpress.com/?s=Favard'` [2012–13 posts]; `curl https://d.lib.msu.edu/etd/1810` [418 bot challenge]; `WebFetch/curl https://pith.science/paper/2509.02882` [machine review flags v1]; Wikipedia API parse Favard_length / Crofton_formula / Buffon's_needle_problem / Cantor_set [no bounds]; `curl https://open.library.ubc.ca/collections/24/items/1.0452055` [blocked]
- C: `msp.org/pjm/2002/204-2/`, `…/p10.xhtml`, `…/pjm-v204-n2-p10-s.pdf` [read]; `iumj.indiana.edu/docs/39011/39011.asp`, `…/FTDLOAD/1990/39/39011/pdf` [OCR read]; `teorth…/60a.html`; `link.springer.com/article/10.1007/s12220-010-9141-4` [auth wall]; `d.lib.msu.edu/etd/1810/datastream/…pdf` [bot check]; `WebFetch d.lib.msu.edu/etd/1810` [TLS error]; `bondmatt…/thesis-7-0.pdf` [read]; `archive.org/wayback/available?…` [429]; `web.archive.org/cdx/…` [listing]; `ams.org/journals/notices/202411/rnoti-p1458.pdf` [HTML / 403]; `WebFetch …/noti3079.html` [403]; `math.stonybrook.edu/~bishop/…/book1Dec15.pdf` [§9.7 read]; `mathnet.ru/eng/rm9556` [abstract only]
- D: `WebFetch https://open.library.ubc.ca/media/download/pdf/24/1.0452055/3` → UBC "unusual activity" block, not bypassed; `WebFetch https://pith.science/paper/2509.02882` → review confirmed (v1, 2026-08-05, deepseek-v4-flash)

### GitHub (`gh`) / git
- A: `gh api -X GET search/issues -f q='repo:teorth/optimizationproblems Favard'` / `'60a'` / `'four-corner'` [0/0/0]; `gh api repos/teorth/optimizationproblems/commits -f path=constants/60a.md` [one commit]; `git remote -v` [origin CoolRmal/FavardLength]
- B: `gh api repos/teorth/optimizationproblems`; `search/code?q=Favard+repo:teorth/optimizationproblems`; `git/trees/main?recursive=1 | grep`; `contents/constants/60a.md`; `commits?path=constants/60a.md`; search/issues for Favard, Buffon, four-corner, Cantor, Garnett, "constant 60", C_60, 60a [all 0 relevant]; `--paginate issues?state=all` [194]; `pulls/{each}/files` [none touches 60a.md]; `git clone …; git log --all -S'Favard'; git log -G'…'` [only a0bc982]; GraphQL discussions [disabled]; `search/repositories` for 'Favard length', 'Favard', 'four-corner Cantor', 'Buffon needle Cantor', 'Garnett set' [only CoolRmal]; `search/code` for '"four-corner Cantor"' [38], '"Favard length" Cantor' [48], '"Nazarov" "Peres" "Volberg" Favard' [15]; contents of u00dxk2/bounds-ledger (mirror, 1/6 and 1), SlopDotCash/proximityprize, linux156/starter-academic, Jim-Vardakis/CV-Resume, az9713/icm-2026 [none relevant]; `gh api repos/CoolRmal/FavardLength`
- C: `git remote -v` in the repo
- D: `gh api repos/teorth/optimizationproblems/commits/main` → 9d57db86, 2026-09-05; `contents/constants/60a.md` → 1/6 ≤ α ≤ 1, unchanged; `commits?path=constants/60a.md` → a0bc982 only; `search/issues q='repo:teorth/optimizationproblems Favard'` → 0; README row 60 → 1/6 and 1; `gh pr list -R teorth/optimizationproblems --state open` → nothing on 60a (latest #194, 2026-09-21)

### StackExchange
- B: `search/excerpts site=mathoverflow` q=Favard | 'four-corner Cantor' | 'Buffon needle Cantor' | 'Garnett set' → no post on four-corner Favard decay

### Local (read-only)
- D: `grep README.md`, `grep references/favard-optimized-quarter-proof.md` → README line 9 misdates Marshall's 1/5 as 2025; the manuscript cites 60a and Marshall v2 §7/§8.5, and its 7/33 is the project's own earlier exponent

## 5. Sources not reached

- **Marshall's UBC PhD dissertation**, *The Favard Length Problem for Self-Similar Sets* (April 2026, DOI 10.14288/1.0452055, hdl 2429/94186). Every route hit UBC bot verification, which was not bypassed. Only the abstract (via OpenAlex) was read, and it states no exponent. It was written after v1 (which claimed 1/4) and before v2 (which withdrew it), so it **may repeat the v1 1/4 claim**. This is the most important gap. A human can open it in a normal browser.
- The Google Scholar "cited by" list for NPV (51 citations) hit a CAPTCHA, which was not attempted. Keyword searches on Scholar did succeed this time.
- The Semantic Scholar snippet (full-text) search and the citations list for 2509.02882 were rate-limited (429) or returned empty. The OpenAlex full-text search partly makes up for this: 18 hits for 2025–26, all checked.
- arXiv full-text search does not exist; coverage relied on metadata search, OpenAlex full text and Google.
- MathSciNet (MR2641082, MR1052016), Web of Science and Scopus: subscription only.
- Journal versions of NPV (SPbMJ), BV (MRL), Łaba–Zhai, BLV, Bond–Volberg (JGA; the Springer page hit an auth wall) and Łaba's survey (Abel volume). Only the arXiv versions were read, plus the zbMATH review of NPV.
- Bond's thesis via the MSU repository (bot check or TLS error). The author's own copy was read instead.
- K. Taylor, Notices AMS 71(11) (2024) (403); Volberg–Eiderman, Russian Math. Surveys 2013 (abstract only); the 2018 Taylor expository record (no PDF); Mattila's 2015 book and the published edition of Bishop–Peres. Mattila 1990, Peres–Solomyak 2002 and the Bishop–Peres 2015 draft were read by report C.
- Marshall, "Finite Good Witnesses …" (2608.10476): found by OpenAlex, and report A grepped it with no claim.
- Conference abstract databases were not searched systematically.

## 6. Calibrated confidence

- **That no valid proof of α_Fav ≥ 1/4 (Fav(K_n) ≲ n^{-1/4+ε}) for the four-corner set was published before this work: about 95%.** Three independent searches plus this verification pass converge. The field's most recent expert statements (Łaba–McDonald–Taylor, July 2026; Marshall v2, August 2026; the registry, September 2026) all place the frontier at 1/6 or 1/5. Marshall v2 explicitly calls the input needed for 1/4 unavailable.
- **That the only prior public assertion of ≥ 1/4 is Marshall v1 (withdrawn), apart from this project's own repo: about 85%.** Most of the remaining doubt is the unread dissertation, which may restate the v1 claim. Next come GS-only or MathSciNet-only citers and non-arXiv venues.
- **Best bound on record before this work:** 1/6 peer-reviewed (NPV; the registry value) and 1/5 in a preprint (Marshall v2, 12 Aug 2026). The upper bound α_Fav ≤ 1 comes from Bateman–Volberg (log n / n) and Mattila (c/n).
