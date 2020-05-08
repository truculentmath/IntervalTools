(* ::Package:: *)

(* ::Title:: *)
(*IntervalTools*)


(* ::Subtitle:: *)
(*Tools for better using the Mathematica's Interval object.*)


BeginPackage["IntervalTools`","QueueStack`"];


(* ::Subtitle:: *)
(*Usage Messages*)


IntervalHull::usage = "IntervalHull[interval1, ...] returns the smallest \
interval that contains all of interval1, ... .";

IntervalWidth::usage = "IntervalWidth[interval] returns the width of interval. \
Returns a list of widths if given a list of intervals.";

IntervalRadius::usage = "IntervalRadius[interval] returns the radius of interval. \
Returns a list of radii if given a list of intervals.";

Magnitude::usage = "IntervalMagnitude[interval] returns the least nonnegative x such \
that interval is contained in Interval[{-x,x}].";

Mignitude::usage = "IntervalMignitude[interval] returns the supremum of nonnegative x such \
that Interval[{-x,x}] does not intersect interval.";

IntervalCorner::usage = "IntervalCorner[{interval1, ...}] returns the corner of the interval \
vector {interval1, ...}, as defined by Gavriliu in thesis."; 

IntervalMidpoint::usage = "IntervalMidpoint[interval] returns the midpoint of interval. \
Returns a list of midpoints if given a list of intervals.";

IntervalEqual::usage = "IntervalEqual[\!\(\*SubscriptBox[\(interval\), \(1\)]\), \!\(\*SubscriptBox[\(interval\), \(2\)]\),...] returns True if all of the \!\(\*SubscriptBox[
StyleBox[\"interval\",\nFontSlant->\"Italic\"], \(i\)]\) have the same Min and Max, and False if the Mins and Maxs are not equal.";

SimplistInteriorPoint::usage  = "SimplistInteriorPoint[interval] returns a point in the interior of interval, with a strong preference for powers of 2. Listable.";

NRange::usage = "NRange[expr,vars,domains] numerically estimates the min and max of expr on domains, which should \
be a list of the same length as vars.";

MonotoneEnclosure::usage = "MonotoneEnclosure[expr,var,interval] assumes that \
expr is monotone and continuous for var \[Element] interval, and returns the resulting interval.  Only works with \
single variable expressions.";

PiecewiseMonotoneEnclosure::usage = "PiecewiseMonotoneEnclosure[expr,var,listofexceptions,interval] \
assumes that expr is continuous and monotone on interval between listofexceptions.";

SplitInterval::usage = "SplitInterval[interval] returns a list of intervals whose union is interval and with smaller widths than interval.
SplitInterval[{\!\(\*SubscriptBox[\(interval\), \(1\)]\), \!\(\*SubscriptBox[\(interval\), \(2\)]\),..}] interprets the list of intervals a box in higher dimensions.";

RationalFunctionQ::usage = "RationalFunctionQ[ expr, ListOfVariables ] returns True if \
expr is transparently a rational function of the variables, and False if this is not \
obvious. Will not perform any simplifications."

IntervalGraphics::usage = "If L is a list of {Interval[{a,b}],Interval[{c,d}]} objects, i.e., rectangles, this makes a \
2-dimensional picture of them.";

RationalizeInterval::usage = "RationalizeInterval[g] returns an interval with rational endpoints \
that contains g. The form Rationalize[g,epsilon] returns an interval that is most epsilon larger \
on each side.";

ProveNonNegative::usage = "ProveNonNegative[f,intervalF,domain] takes a function, an \
interval enclosure of the function, and a domain, and returns a \
triple {fails,uncertain,settled} giving arguments where the function f is negative, \
where the sign could not be determined, and where the function f is proved nonnegative. \
If certificate->False is used as an option, then only the last example of each \
is returned. Also, MaxDepth->10 can be changed.";

IntervalIntegrate::usage = "IntervalIntegrate[intervalF, interval, errorbound] takes an \
interval enclosure, a domain, and an errorbound, and keeps subdividing interval \
until the integral is bounded above and below within errorbound.";

SimpleSolve::usage  =  "SimpleSolve[f, intervalF, domain, epsilon] returns a list of intervals, each \
with maximum width less than epsilon, that is guaranteed to contain all of the roots of f.";

NewtonsMethod::usage = "NewtonsMethod[f, intervalF, domain] returns an interval that is guaranteed \
to contain all solutions to f[x]==0 with x in domain. The pure function intervalF must \
be an interval enclosure of the derivative of f. Only works with single variable functions.";

MooreSkelboeMinimize::usage = "MooreSkelboeMinimize[f, intervalF, domain, domaintolerance] returns \
an interval that is proven to contain the infimum of f on domain (a list of simple intervals) \
and a list of subdomains that is guaranteed to contain all points where the infimum occurs. The option \
certificate -> False returns only a guess for where the minimum may occur, by averaging the \
certificate. The method is Moore-Skelboe, and the algorithm proceeds until all of the domains \
being inspected have either been eliminated or have width at most domaintolerance. Beware \
of calling this function with domaintolerance too small.";


(* ::Subtitle:: *)
(*Additional Primitive Interval Enclosures*)


(* ::Text:: *)
(*These extensions assume infinite precision!*)


(* ::Subsubsection:: *)
(*Zeta*)


(* ::Text:: *)
(*Only  for  arguments at least 1.*)


Unprotect[Interval];
Interval/:Zeta[g_Interval/;IntervalMemberQ[Interval[{1,Infinity}],g]]:=
	Interval[{If[Min[g]==1,Infinity,Zeta[Min[g]]],If[Max[g]==Infinity,1,Zeta[Max[g]]]}];
Interval/:Zeta[Interval[]]=Interval[];
Interval/:Zeta[g_Interval/; Min[g]<1 ]:= Interval[{-Infinity,Infinity}];
Protect[Interval];


Unprotect[Interval];
Interval/:Zeta'[g_Interval/;IntervalMemberQ[Interval[{1,Infinity}],g]]:=
	Interval[{If[Min[g]==1,-Infinity,Zeta'[Min[g]]],If[Max[g]==Infinity,0,Zeta'[Max[g]]]}];
Interval/:Zeta'[Interval[]]=Interval[];
Interval/:Zeta'[g_Interval/; Min[g]<1 ]:= Interval[{-Infinity,Infinity}];
Protect[Interval];


(* ::Subsection:: *)
(*CubeRoot*)


Unprotect[Interval];
Interval /: CubeRoot[g_Interval] := Map[CubeRoot,g];
Protect[Interval];


(* ::Subsection:: *)
(*Surd*)


Unprotect[Interval];
Interval /: Surd[g_Interval,n_Integer] := Map[Surd[#,n]&,g];
Protect[Interval];


(* ::Subtitle::Closed:: *)
(*Begin Private*)


Begin["`Private`"]


(* ::Subtitle:: *)
(*Actual Code*)


(* ::Section::Closed:: *)
(*Interval Operations*)


IntervalHull[g___Interval]:=Interval[{Min[Map[Min,{g}]],Max[Map[Max,{g}]]}];
IntervalHull[]=Interval[];
IntervalHull[g_Real] := Interval[g];


SetAttributes[IntervalWidth,Listable];
IntervalWidth[g_Interval] := Max[g]-Min[g];
IntervalWidth[g_Real]=0;
(* IntervalWidth[Interval[]] is 0, Infinity, or undefined? *)


SetAttributes[IntervalRadius,Listable];
IntervalRadius[g_Interval] := (Max[g]-Min[g])/2;
IntervalRadius[g_Real] := 0;


SetAttributes[Mignitude,Listable];
Mignitude[g_Interval] := If[IntervalMemberQ[g,0],0,Min[Abs[Max[g]],Abs[Min[g]]]];
Mignitude[g_Real]  := Abs[g];


SetAttributes[Magnitude,Listable];
Magnitude[g_Interval] := Max[Abs[Max[g]],Abs[Min[g]]];
Magnitude[g_Real] := Abs[g];


SetAttributes[IntervalSign,Listable];
IntervalSign[g_Interval] := Which[Max[g]<=0,  -1, Min[g]>=0,  1, True, 0];


SetAttributes[IntervalMidpoint,Listable];
IntervalMidpoint[g_Interval] := (Max[g] + Min[g]) / 2;


SetAttributes[IntervalCorner,Listable];
IntervalCorner[g_Interval] := Which[IntervalMemberQ[g,0],0,Min[g]>0,Min[g],True,Max[g]];


IntervalEqual[g_Interval] := True;
IntervalEqual[g_Interval,h_Interval] := Min[g]==Min[h] && Max[g]==Max[h];
IntervalEqual[g_Interval, h_Interval, j__Interval] := IntervalEqual[g,h] && IntervalEqual[h,j];


SetAttributes[SimplistInteriorPoint,Listable];
SimplistInteriorPoint[Interval[]]=Undefined;
SimplistInteriorPoint[g_Interval]:=
	Module[{birthday=0,a,b,sp1,sp2},
		{a,b}=MinMax[g];
		Which[
			b==a,   
				Undefined,
			a<0<b, 
				0,
			a==-Infinity,
				If[b==0, -1, -2^Floor[Log[2,-b]+1]],
			b==Infinity,
				If[a==0, 1, 2^Floor[Log[2,a]+1]],
			True,
				While[
					sp1=Floor[a,2^-birthday]+2^-birthday;
					sp2=Ceiling[b,2^-birthday]-2^-birthday;
					sp1!=sp2,
					If[sp1<sp2,birthday--,birthday++]];
				sp1
		]
	];


SplitInterval[g_Interval]:=
	Module[{sip=SimplistInteriorPoint[g]},
		{Interval[{Min[g],sip}],Interval[{sip,Max[g]}]}];

SplitInterval[box_List] := SplitInterval[box, Method -> "Every Dimension"];
SplitInterval[box_List, Method -> "Every Dimension"]:=
	Module[{dim=Length[box],where,simple,newgap,digs},
		simple=SimplistInteriorPoint[box];
		newgap[0]=Table[Interval[{Min[box[[where]]],simple[[where]]}],{where,dim}];
		newgap[1]=Table[Interval[{simple[[where]],Max[box[[where]]]}],{where,dim}];

		Table[digs=IntegerDigits[n,2,dim];
		Table[newgap[digs[[k]]][[k]],{k,dim}],{n,0,2^dim-1}]];
		
SplitInterval[box_List, Method->"Fattest Dimension"]:=
	Module[{lengths,maxlen,where,simple,newgap1,newgap2},
		lengths=IntervalWidth[box];
		maxlen=Max[lengths];
		where=RandomChoice[Flatten[Position[lengths,maxlen]]];
		simple=SimplistInteriorPoint[box[[where]]];
		newgap1=Interval[{Min[box[[where]]],simple}];
		newgap2=Interval[{simple,Max[box[[where]]]}];
		{ReplacePart[box,where->newgap1],ReplacePart[box,where->newgap2]}];
		
SplitInterval[box_List, Method->"Random Dimension"]:=
	Module[{where,simple,newgap1,newgap2},
		where=RandomChoice[Range[Length[box]]];
		simple=SimplistInteriorPoint[box[[where]]];
		newgap1=Interval[{Min[box[[where]]],simple}];
		newgap2=Interval[{simple,Max[box[[where]]]}];
		{ReplacePart[box,where->newgap1],ReplacePart[box,where->newgap2]}];
		
SplitInterval[box_List, Method->"Each Dimension"]:=
	Module[{where,simple,newgap1,newgap2},
		Flatten[
		  Table[
			simple=SimplistInteriorPoint[box[[where]]];
			newgap1=Interval[{Min[box[[where]]],simple}];
			newgap2=Interval[{simple,Max[box[[where]]]}];
			{ReplacePart[box,where->newgap1],ReplacePart[box,where->newgap2]},
		  {where,Length[box]}]]]


(* ::Section::Closed:: *)
(*Helper Functions*)


RationalFunctionQ[expr_,vars_]:=Which[
Max[Map[Count[expr,#,All]&,vars]]==0,
	True,
Head[expr]===Plus||Head[expr]===Times,
	And[RationalFunctionQ[First[expr],vars],RationalFunctionQ[Rest[expr],vars]],
Head[expr]===Symbol,
	True,
Head[expr]===Power,
	IntegerQ[Last[expr]]&&RationalFunctionQ[First[expr],vars],
True,
	False];


RationalizeInterval[g_Interval,prec_:2^-50]:=Module[{RoundDown,RoundUp},
RoundDown[num_]:=Module[{a,q,p,alpha,r,beta},
{p[-1],q[-1]}={1,0};
{p[0],q[0]}={Floor[num],1};
a[0]=p[0];
alpha[0]=num-a[0];
r=0;
While[alpha[r]>0&&(OddQ[r]||num-p[r]/q[r]>=prec),
beta=1/alpha[r];
a[r+1]=Floor[beta];
alpha[r+1]=beta-a[r+1];
{p[r+1],q[r+1]}=a[r+1]{p[r],q[r]}+{p[r-1],q[r-1]};
r++];
Return[p[r]/q[r]]];
RoundUp[num_]:=Module[{a,q,p,alpha,r,beta},
{p[-1],q[-1]}={1,0};
{p[0],q[0]}={Floor[num],1};
a[0]=p[0];
alpha[0]=num-a[0];
r=0;
While[alpha[r]>0&&(EvenQ[r]||p[r]/q[r]-num>=prec),
beta=1/alpha[r];
a[r+1]=Floor[beta];
alpha[r+1]=beta-a[r+1];
{p[r+1],q[r+1]}=a[r+1]{p[r],q[r]}+{p[r-1],q[r-1]};
r++];
Return[p[r]/q[r]]];
Map[{RoundDown[Min[#]],RoundUp[Max[#]]}&,g]]


(* ::Section::Closed:: *)
(*Graphics*)


IntervalGraphics[g_Interval]:=If[
IntervalWidth[g]==0,Graphics[Point[{0,Min[g]}]],
Graphics[Union[Map[{Line[{{Min[#],0},{Max[#],0}}],Point[{Min[#],0}],Point[{Max[#],0}]}&,
List@@g]]]];



IntervalGraphics[L_List,domain_,opts___]:=
	Block[
	{domtorect={Interval[{a_,b_}],Interval[{c_,d_}]}:>Rectangle[{a,c},{b,d}],tiny,diameter},
	If[Length[L]>=1&&Length[domain]===2,
		diameter = Max[Table[IntervalWidth[domain[[i]]]/IntervalWidth[L[[1]][[i]]],{i,2}]];
		If[diameter<100,
			Graphics[Join[{EdgeForm[Directive[Thin,Dashed,Blue]],LightGray,opts},
							L/.domtorect],
							PlotRange->{MinMax[domain[[1]]],MinMax[domain[[2]]]},
							AspectRatio->1],
			Graphics[Join[{LightGray,opts},
							L/.domtorect],
							PlotRange->{MinMax[domain[[1]]],MinMax[domain[[2]]]},
							AspectRatio->1]],
		Null]];


(* ::Section::Closed:: *)
(*Odds and Ends for enclosures*)


NRange[expr_,vars_,domains_]:=Module[{logicaldomain},
	logicaldomain = Table[Min[domains[[i]]]<=vars[[i]]<=Max[domains[[i]]],{i,Length[vars]}];
	{First[NMinimize[{expr,logicaldomain},vars]],
	First[NMaximize[{expr,logicaldomain},vars]]}];


MonotoneEnclosure[expr_,var_,int_Interval]:=
	Which[
	IntervalWidth[int]>0,
	Interval[{Limit[expr,var->Min[int],Direction->"FromAbove"],Limit[expr,var->Max[int],Direction->"FromBelow"]}],
	int===Interval[], Interval[],
	True,
	expr/.var->Min[int]];


PiecewiseMonotoneEnclosure[expr_,var_,criticalvalues_List,int_Interval]:=
	Which[
	int===Interval[],Interval[],
	IntervalWidth[int]==0,expr/.var->Min[int],
	True,
	Module[{left,right,crits,vals},
		crits=Select[criticalvalues,Min[int]<#<Max[int]&];
		left=Limit[expr,var->Min[int],Direction->"FromAbove"];
		right=Limit[expr,var->Max[int],Direction->"FromBelow"];
		If[crits==={},Interval[{left,right}],
			vals=Join[{left,right},Map[Limit[expr,var->#]&,crits]];
			Interval[MinMax[vals]]]]];


(* ::Section::Closed:: *)
(*Solving Equations*)


Options[SimpleSolve]={SplittingMethod->"Fattest Dimension"};
SimpleSolve[f_,gapF_,box_List,domainepsilon_,OptionsPattern[]] :=
	Module[{x,y,sdm,counter=0,IB,workingstack,finishedstack,output},
		StackPush[workingstack,box];
		While[Not[StackEmpty[workingstack]],
			x=StackPop[workingstack];
			y=gapF@@x;
			If[IntervalMemberQ[y,0],
				If[Max[IntervalWidth[x]] <= domainepsilon,
					StackPush[finishedstack,IB@@x],
					sdm=SplitInterval[x, SplittingMethod->OptionValue[SplittingMethod]];
					Map[StackPush[workingstack,#]&,sdm]
					]
				]
			];(* end while *)
		output=StackList[finishedstack]/.IB->List;
		StackClear[{workingstack,finishedstack}];
		Return[output]
		](* end module *);	


(* This is one-dimensional Newton's Method *)
Options[NewtonsMethod]={PrecisionGoal->8,AccuracyGoal->8,MaxRecursion->10};
NewtonsMethod[f_,df_,domain_Interval,OptionsPattern[]]:=
	Module[{epsilonbase,NO,WorkOnInterval},
		epsilonbase=10^-{OptionValue[AccuracyGoal],OptionValue[PrecisionGoal]};

		NO[dom_Interval]:=Block[{m=IntervalMidpoint[dom]},IntervalIntersection[dom,m-f[m]/df[dom]]];

		WorkOnInterval[dom_,0]:=dom;
		WorkOnInterval[dom_,n_]:=(*dom should be Interval[{a,b}]*)
			Module[{epsilon=epsilonbase.{1,Max[dom]},newdomain},
				If[
					IntervalWidth[dom]<epsilon,
					dom,

					newdomain=RationalizeInterval[NO[dom],epsilon/4];
					IntervalUnion@@Map[WorkOnInterval[Interval[#],n-1]&,List@@newdomain]]];

	IntervalUnion@@Map[WorkOnInterval[Interval[#],OptionValue[MaxRecursion]]&,List@@domain]]


(* ::Section::Closed:: *)
(*Proving Inequalities*)


Options[ProveNonNegative]={certificate->True,MaxDepth->10,SplittingMethod -> "Every Dimension"};
ProveNonNegative[F_,gapF_,box_List,OptionsPattern[]]:=
	Module[
	{GoDeeper,
	 stillworking=True,
	 works={},unsettled={},fails={},
	 v=Length[box]},

	GoDeeper[depth_,sdm_]:=
		Module[
		{tb=gapF@@sdm,middles,value},
		If[Min[tb]>=0,
			works=If[OptionValue[certificate],{works,sdm},sdm],

			middles=SimplistInteriorPoint[sdm];
			value=F@@middles;
			If[Negative[value],
				fails={middles,N[value,50]};
				stillworking=False];

			If[stillworking,
				If[depth==0,
					unsettled=If[OptionValue[certificate],{unsettled,sdm},sdm],
					Map[GoDeeper[depth-1,#1]&,SplitInterval[sdm,Method->OptionValue[SplittingMethod]]]
				],
				unsettled=If[OptionValue[certificate],{unsettled,sdm},sdm]]]];

	GoDeeper[OptionValue[MaxDepth],box];

	{fails,
	Partition[Flatten[unsettled],Length[box]],
	Partition[Flatten[works],Length[box]]}]


(* ::Section:: *)
(*Integration*)


Options[IntervalIntegrate]={ErrorBound->10^-4,DomainBound->10^-5};

IntervalIntegrate[gapF_,domain_Interval,OptionsPattern[]]:=
	Module[
		{internalIntegrate,
		domrat=OptionValue[DomainBound]*IntervalWidth[domain]},
	
	If[IntervalWidth[domain]==0,Return[Interval[0]]];

	internalIntegrate[dom_,eb_]:=
		Module[
			{length,ints,diameters,values,current,one,two},
		
		ints=SplitInterval[dom];
		diameters=Map[IntervalWidth,ints];
		values=Map[gapF,ints]*diameters;
		current=Plus@@values;
		length=IntervalWidth[dom];
		
		If[Or[length < domrat,IntervalWidth[current]<eb],Return[current]];

		one = N[internalIntegrate[ints[[1]],eb*diameters[[1]]/length],30];
		two = N[internalIntegrate[ints[[2]],eb*diameters[[2]]/length],30];
		Return[one + two]];

	internalIntegrate[domain,OptionValue[ErrorBound]]
	];


(* ::Section::Closed:: *)
(*Global Optimization*)


Options[MooreSkelboeMinimize]={certificate->True,SplittingMethod -> "Fattest Dimension"};

MooreSkelboeMinimize[F_,gapF_,box_List,domaintolerance_,OptionsPattern[]]:=
Module[
{infub=\[Infinity],inflb,dig,corner,n,likely,plausible,sdm,int,newpairs,newval,infwhere},

QueuePush[plausible,{gapF@@box,box}];
(* specifically look for  the min to happen at a corner *)
Do[
dig=IntegerDigits[n,2,Length[box]];
corner=Table[If[dig[[i]]==0,Min[box[[i]]],Max[box[[i]]]],{i,Length[box]}];
infub=Min[infub,F@@corner],
{n,0,2^Length[box]-1}];

While[Not[QueueEmpty[plausible]],
{int,sdm}=QueuePop[plausible];
If[Min[int]<=infub,
If[Max@@IntervalWidth[sdm]<=domaintolerance,

QueuePush[likely,{int,sdm}],

If[newval=F@@SimplistInteriorPoint[sdm];newval<infub,
infub=newval;
QueueSelect[plausible,plausible,Min[First[#]]<=infub&]
];

newpairs=Map[{gapF@@#,#}&,SplitInterval[sdm,Method->OptionValue[SplittingMethod]]];
newpairs=Select[newpairs,Min[First[#]]<=infub&];
newpairs=Sort[newpairs,Min[First[#1]]<Min[First[#2]]&];
Map[QueuePush[plausible,#]&,newpairs]]]];

QueueSelect[likely,likely,Min[First[#]]<=infub&];
infwhere=QueueList[likely];

QueueClear[likely,plausible];

inflb=Min@@Map[Min[First[#]]&,infwhere];
infwhere=Last/@infwhere;

{Interval[{inflb,infub}],If[OptionValue[certificate],infwhere,Mean[infwhere]]}]


(* ::Subtitle:: *)
(*End the package*)


End[]
EndPackage[]
