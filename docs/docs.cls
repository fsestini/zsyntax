\NeedsTeXFormat{LaTeX2e}
\ProvidesClass{docs}[]
%% \LoadClass[a4paper]{article}
\LoadClass{article}

\RequirePackage{float}
\RequirePackage{amsmath}
\RequirePackage{amssymb}
\RequirePackage{dsfont}
\RequirePackage{prooftree}
\RequirePackage{amsthm}
\RequirePackage{thmtools}
\RequirePackage{mathtools}
\RequirePackage{mdframed}
\RequirePackage{array}% for \newcolumntype macro
\RequirePackage{cite}

\newcolumntype{L}{>{$}l<{$}} % math-mode version of "l" column type

% \hypersetup{
%     pdftex,
%     pdfpagemode=UseOutlines
%   }

\theoremstyle{definition}
\newtheorem{example}{Example}[section]
\newtheorem{exercise}{Exercise}[section]
\newtheorem{proposition}{Proposition}[section]
\newtheorem{theorem}{Theorem}[section]
\declaretheorem[name=Definition,qed={\lower-0.3ex\hbox{$\blacksquare$}}]{definition}
\newtheorem{lemma}{Lemma}[section]
\newtheorem{corollary}{Corollary}[section]
\newtheorem{notation}{Notation}[section]
\newtheorem{fact}{Fact}[section]

\def\limp {\mathbin{{-}\mkern-3.5mu{\circ}}} %% Linear implication symbol

\newcommand\mdoubleplus{\mathbin{+\mkern-10mu+}}
\newcommand{\listplus}[2]{#1 \mdoubleplus #2}
\newcommand{\basepluslist}[2]{#1 \cdot #2}
\newcommand{\resplist}[2]{#1 \dagger #2}
\newcommand{\reactlist}[1]{l_{#1}}
\newcommand{\baseandplus}[3]{\listplus{\basepluslist{#1}{#2}}{#3}}
\newcommand{\emptyctrl}{[]}

% Standard backward sequents
\newcommand{\bkwseq}[3]{#1 ; #2 \Longrightarrow #3}
\newcommand{\zsyseq}[4]{#1 ; #2 \Longrightarrow_{#3} #4}
\newcommand{\zsyseqw}[5]{#1 ; #2 \Longrightarrow_{#3}^{#4} #5}

\newcommand{\znd}{\textsf{Z}}
\newcommand{\eznd}{\textsf{EZ}}
\newcommand{\zss}{\textsf{ZS}}

% Standard forward sequents
\newcommand{\fwdseq}[3]{#1 ; #2 \longrightarrow #3}
\newcommand{\zfwdseq}[4]{#1 ; #2 \longrightarrow_{#3} #4}

% backward and forward neutral sequents symbols and macros
\newcommand{\bneuseqsymb}{
  \mathrel{\Longrightarrow\!\!\!\!\!\!\!\!\Longrightarrow}}
% \newcommand{\fneuseqsymb}{\twoheadrightarrow}
\newcommand{\fneuseqsymb}{
  \mathrel{\longrightarrow\!\!\!\!\!\!\!\!\longrightarrow}}
\newcommand{\bneuseq}[3]{#1 ; #2 \bneuseqsymb #3}
\newcommand{\zbneuseq}[4]{#1 ; #2 \bneuseqsymb_{#3} #4}
\newcommand{\fneuseq}[3]{#1 ; #2 \fneuseqsymb #3}
\newcommand{\zfneuseqempty}[2]{#1 ; #2 \fneuseqsymb \cdot}
\newcommand{\zfneuseq}[4]{#1 ; #2 \fneuseqsymb_{#3} #4}

% backward derived-rule relations
\newcommand{\brfrel}[1]{\textsf{foc}^+_{\Uparrow}(#1)}
\newcommand{\blfrel}[1]{\textsf{foc}^-_{\Uparrow}(#1)}
\newcommand{\bactrel}[1]{\textsf{act}_{\Uparrow}(#1)}

% forward derived-rule relations
\newcommand{\frfrel}[1]{\textsf{foc}^+_{\Downarrow}(#1)}
\newcommand{\flfrel}[1]{\textsf{foc}^-_{\Downarrow}(#1)}
\newcommand{\factrel}[1]{\textsf{act}_{\Downarrow}(#1)}

% Relation judgement   rel[...] ~--> res
\newcommand{\relj}[3]{#1 [#2] \hookrightarrow #3}

% Relation + judgement
\newcommand{\brfrelj}[3]{\relj{\brfrel{#1}}{#2}{#3}}
\newcommand{\blfrelj}[3]{\relj{\blfrel{#1}}{#2}{#3}}
\newcommand{\bactrelj}[3]{\relj{\bactrel{#1}}{#2}{#3}}
\newcommand{\frfrelj}[3]{\relj{\frfrel{#1}}{#2}{#3}}
\newcommand{\flfrelj}[3]{\relj{\flfrel{#1}}{#2}{#3}}
\newcommand{\factrelj}[3]{\relj{\factrel{#1}}{#2}{#3}}

% Three-place bold sequents     G, D, O ===> C
\newcommand{\btriseq}[4]{#1; #2; #3 \Longrightarrow #4}

% Focusing sequents
\newcommand{\rfocseq}[3]{#1; #2 \gg #3}
\newcommand{\lfocseq}[4]{#1; #2; #3 \ll #4}

% Bio focusing sequent
\newcommand{\ztriseq}[5]{#1; #2; #3 \Longrightarrow_{#4} #5}
\newcommand{\zqseq}[6]{#1; #2; #3; #4 \Longrightarrow_{#5} #6}
\newcommand{\zqseqem}[5]{#1; #2; #3; #4 \Longrightarrow_{\emptyset} #5}
\newcommand{\zqseqct}[6]{#1; #2; #3; #4 \Longrightarrow_{\ctrlset{#5}} #6}
\newcommand{\zfocseq}[3]{#1; #2 \gg_{\emptyset} #3}

% Rule labels
\newcommand{\init}{\textsc{init}}
\newcommand{\rinit}{\textsc{rinit}}
\newcommand{\linit}{\textsc{linit}}
\newcommand{\lact}{\textsc{lact}}
\newcommand{\ract}{\textsc{ract}}
\newcommand{\bact}{\textsc{bact}}
\newcommand{\rfoc}{\textsc{rfoc}}
\newcommand{\lfoc}{\textsc{lfoc}}
\newcommand{\actrule}{\textsc{act}}
\newcommand{\matchrule}{\textsc{match}}
\newcommand{\matchprimerule}{\textsc{match'}}
\newcommand{\rightfocusrule}{\textsc{right-focus}}
\newcommand{\leftfocusrule}{\textsc{left-focus}}
\newcommand{\copyfocusrule}{\textsc{copy-focus}}
\newcommand{\rblur}{\textsc{rblur}}
\newcommand{\lblur}{\textsc{lblur}}
\newcommand{\rblurstar}{\textsc{rblur}^*}
\newcommand{\lblurstar}{\textsc{lblur}^*}
\newcommand{\faplus}{\textsc{FA}^+}
\newcommand{\faminus}{\textsc{FA}^-}
\newcommand{\faplusstar}{\textsc{FA}^{+*}}
\newcommand{\faminusstar}{\textsc{FA}^{-*}}
\newcommand{\copyrule}{\textsc{copy}}
\newcommand{\focplusrule}{\textsf{foc}^+_{\Downarrow}}
\newcommand{\focminusrule}{\textsf{foc}^-_{\Downarrow}}
\newcommand{\foccopyrule}{\textsf{!foc}^-_{\Downarrow}}


\newcommand{\zsy}[3]{#1 \ \models_{#2} \ #3}
\newcommand{\biocore}[1]{(#1)^{*}}
\newcommand{\deflimp}{\limp^{S}_{\ctrlset{}}}

% All elementary bases of a formula/context
\newcommand{\elembases}[1]{(#1)^{b}}
\newcommand{\elembasesw}[2]{(#1)^{b}_{#2}}

% Bonding language
\newcommand{\bioformulas}{\mathcal{L}_{\odot}}

\newcommand{\css}[1]{\mathrm{CSS}_{#1}}
\newcommand{\bss}[1]{\mathrm{BSS}_{#1}}

\newcommand{\ctrlset}[1]{\mathfrak{S}_{#1}}

\newcommand{\respects}[2]{#1 \| #2}
\newcommand{\plainrespects}[2]{#1 \, || \, #2}

\newcommand{\labels}[2]{#1 \, \# \, #2}

\newcommand{\strong}[1]{\textbf{#1}}

\newcommand{\subsequent}[2]{#1 \leq #2}
\newcommand{\frwdseq}[3]{#1 ; #2 \longrightarrow #3}

\newcommand{\tyj}[2]{#1 : #2}
\newcommand{\seqpt}[2]{#1 \, :: \, #2}

% Formula decoration
\newcommand{\decplus}[1]{#1^+}
\newcommand{\decminus}[1]{#1^-}
\newcommand{\declinear}[1]{#1_.}
\newcommand{\decunrestr}[1]{#1_!}
\newcommand{\decpluslinear}[1]{\decplus{\declinear{#1}}}
\newcommand{\decminuslinear}[1]{\decminus{\declinear{#1}}}
\newcommand{\decminusunrestr}[1]{\decminus{\decunrestr{#1}}}
\newcommand{\decplusminus}[1]{#1^{\pm}}
\newcommand{\decminusplus}[1]{#1^{\mp}}

% Derivation terms
\newcommand{\dtinit}[1]{\textsf{init}(#1)}
\newcommand{\dtcopy}[2]{\textsf{copy}(#1, #2)}
\newcommand{\dtotimesr}[2]{\otimes \textsf{R}(#1, #2)}
\newcommand{\dtotimesl}[3]{\otimes \textsf{L}(#1, #2, #3)}
\newcommand{\dtlimpr}[2]{\limp \textsf{R}(#1, #2)}
\newcommand{\dtlimpl}[5]{\limp \textsf{L}(#1, #2, #3, #4, #5)}

% % Labelled derivation terms
% \newcommand{\dtinit}[1]{\textsf{init}(#1)}
% \newcommand{\dtcopy}[3]{\textsf{copy}(#1, \labels{#2}{#3})}
% \newcommand{\dtotimesr}[4]{\otimes \textsf{R}(#1, #2 ; \labels{#3}{#4})}
% \newcommand{\dtotimesl}[7]{\otimes
%   \textsf{L}(#1, \labels{#2}{#3}, \labels{#4}{#5} ; \labels{#6}{#7})}
% \newcommand{\dtlimpr}[5]{\limp \textsf{R}(#1, \labels{#2}{#3}
%   ; \labels{#4}{#5})}
% \newcommand{\dtlimpl}[6]{\limp \textsf{L}(#1, #2, \labels{#3}{#4} ; \labels{#5}{#6})}
% \newcommand{\dtfactor}[5]{\textsf{factor}(#1 . #2 . #3 ; \tyj{#4}{#5})}

% Haskell terms
\newcommand{\relsym}{\textsf{Rel}}
\newcommand{\relty}[2]{\relsym\ #1\ #2}
\newcommand{\inl}{\textsf{inl}}
\newcommand{\inr}{\textsf{inr}}