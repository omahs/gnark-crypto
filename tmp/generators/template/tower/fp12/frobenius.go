package fp12

const Frobenius = `
// Frobenius set z to Frobenius(x) in {{.Fp12Name}} and return z
func (z *{{.Fp12Name}}) Frobenius(x *{{.Fp12Name}}) *{{.Fp12Name}} {
	// Algorithm 28 from https://eprint.iacr.org/2010/354.pdf (beware typos!)
	var t [6]{{.Fp2Name}}

	// Frobenius acts on fp2 by conjugation
	t[0].Conjugate(&x.C0.B0)
	t[1].Conjugate(&x.C0.B1)
	t[2].Conjugate(&x.C0.B2)
	t[3].Conjugate(&x.C1.B0)
	t[4].Conjugate(&x.C1.B1)
	t[5].Conjugate(&x.C1.B2)

	t[1].MulByNonResiduePower2(&t[1])
	t[2].MulByNonResiduePower4(&t[2])
	t[3].MulByNonResiduePower1(&t[3])
	t[4].MulByNonResiduePower3(&t[4])
	t[5].MulByNonResiduePower5(&t[5])

	z.C0.B0 = t[0]
	z.C0.B1 = t[1]
	z.C0.B2 = t[2]
	z.C1.B0 = t[3]
	z.C1.B1 = t[4]
	z.C1.B2 = t[5]

	return z
}

// FrobeniusSquare set z to Frobenius^2(x) in {{.Fp12Name}} and return z
func (z *{{.Fp12Name}}) FrobeniusSquare(x *{{.Fp12Name}}) *{{.Fp12Name}} {
	// Algorithm 29 from https://eprint.iacr.org/2010/354.pdf (beware typos!)
	var t [6]{{.Fp2Name}}

	t[1].MulByNonResiduePowerSquare2(&x.C0.B1)
	t[2].MulByNonResiduePowerSquare4(&x.C0.B2)
	t[3].MulByNonResiduePowerSquare1(&x.C1.B0)
	t[4].MulByNonResiduePowerSquare3(&x.C1.B1)
	t[5].MulByNonResiduePowerSquare5(&x.C1.B2)

	z.C0.B0 = x.C0.B0
	z.C0.B1 = t[1]
	z.C0.B2 = t[2]
	z.C1.B0 = t[3]
	z.C1.B1 = t[4]
	z.C1.B2 = t[5]

	return z
}

// FrobeniusCube set z to Frobenius^3(x) in {{.Fp12Name}} and return z
func (z *{{.Fp12Name}}) FrobeniusCube(x *{{.Fp12Name}}) *{{.Fp12Name}} {
	// Algorithm 30 from https://eprint.iacr.org/2010/354.pdf (beware typos!)
	var t [6]{{.Fp2Name}}

	// Frobenius^3 acts on fp2 by conjugation
	t[0].Conjugate(&x.C0.B0)
	t[1].Conjugate(&x.C0.B1)
	t[2].Conjugate(&x.C0.B2)
	t[3].Conjugate(&x.C1.B0)
	t[4].Conjugate(&x.C1.B1)
	t[5].Conjugate(&x.C1.B2)

	t[1].MulByNonResiduePowerCube2(&t[1])
	t[2].MulByNonResiduePowerCube4(&t[2])
	t[3].MulByNonResiduePowerCube1(&t[3])
	t[4].MulByNonResiduePowerCube3(&t[4])
	t[5].MulByNonResiduePowerCube5(&t[5])

	z.C0.B0 = t[0]
	z.C0.B1 = t[1]
	z.C0.B2 = t[2]
	z.C1.B0 = t[3]
	z.C1.B1 = t[4]
	z.C1.B2 = t[5]

	return z
}

{{ define "MulByNonResiduePowerHeader" }}
	// MulByNonResiduePower{{$.vars.powerName}}{{$.vars.powerNum}} set z=x*({{$.all.Fp6NonResidue}})^({{$.vars.powerNum}}*(p{{$.vars.pComment}}-1)/6) and return z
	func (z *{{$.all.Fp2Name}}) MulByNonResiduePower{{$.vars.powerName}}{{$.vars.powerNum}}(x *{{$.all.Fp2Name}}) *{{$.all.Fp2Name}} {
		// ({{$.all.Fp6NonResidue}})^({{$.vars.powerNum}}*(p{{$.vars.pComment}}-1)/6)
{{- end }}

{{ define "MulByNonResiduePowerFp" }}
	{{- template "MulByNonResiduePowerHeader" dict "all" $.all "vars" . }}
	{{- if (eq $.betaDecimal "1") }}
		// the value is 1; nothing to do
	{{- else }}
		// {{$.betaDecimal}}
		b := fp.Element{
			{{$.betaArray}}
		}
		z.A0.Mul(&x.A0, &b)
		z.A1.Mul(&x.A1, &b)
	{{- end }}
	return z
}
{{- end }}

{{ define "MulByNonResiduePowerFp2" }}
	{{- template "MulByNonResiduePowerHeader" dict "all" $.all "vars" . }}
	// {{$.betaDecimal}} + u*{{$.betaDecimalU}}
	b := e2{
		A0: fp.Element{
			{{$.betaArray}}
		},
		A1: fp.Element{
			{{$.betaArrayU}}
		},
	}
	z.Mul(x, &b)
	return z
}
{{- end }}

{{- /* TODO generate all these constants automatically using sage or big.Int */}}
{{- if and (eq .Fp6NonResidue "0,1") (eq .FpModulus "258664426012969094010652733694893533536393512754914660539884262666720468348340822774968888139573360124440321458177") }}

	{{- template "MulByNonResiduePowerFp" dict "all" . "powerNum" 1 "powerName" "" "pComment" "" "betaDecimal" "92949345220277864758624960506473182677953048909283248980960104381795901929519566951595905490535835115111760994353" "betaArray" "7981638599956744862,\n11830407261614897732,\n6308788297503259939,\n10596665404780565693,\n11693741422477421038,\n61545186993886319," }}

	{{- template "MulByNonResiduePowerFp" dict "all" . "powerNum" 2 "powerName" "" "pComment" "" "betaDecimal" "80949648264912719408558363140637477264845294720710499478137287262712535938301461879813459410946" "betaArray" "6382252053795993818,\n1383562296554596171,\n11197251941974877903,\n6684509567199238270,\n6699184357838251020,\n19987743694136192," }}

	{{- template "MulByNonResiduePowerFp" dict "all" . "powerNum" 3 "powerName" "" "pComment" "" "betaDecimal" "216465761340224619389371505802605247630151569547285782856803747159100223055385581585702401816380679166954762214499" "betaArray" "10965161018967488287,\n18251363109856037426,\n7036083669251591763,\n16109345360066746489,\n4679973768683352764,\n96952949334633821," }}

	{{- template "MulByNonResiduePowerFp" dict "all" . "powerNum" 4 "powerName" "" "pComment" "" "betaDecimal" "80949648264912719408558363140637477264845294720710499478137287262712535938301461879813459410945" "betaArray" "15766275933608376691,\n15635974902606112666,\n1934946774703877852,\n18129354943882397960,\n15437979634065614942,\n101285514078273488," }}

	{{- template "MulByNonResiduePowerFp" dict "all" . "powerNum" 5 "powerName" "" "pComment" "" "betaDecimal" "123516416119946754630746545296132064952198520638002533875843642777304321125866014634106496325844844051843001220146" "betaArray" "2983522419010743425,\n6420955848241139694,\n727295371748331824,\n5512679955286180796,\n11432976419915483342,\n35407762340747501," }}

	{{- template "MulByNonResiduePowerFp" dict "all" . "powerNum" 1 "powerName" "Square" "pComment" "^2" "betaDecimal" "80949648264912719408558363140637477264845294720710499478137287262712535938301461879813459410946" "betaArray" "6382252053795993818,\n1383562296554596171,\n11197251941974877903,\n6684509567199238270,\n6699184357838251020,\n19987743694136192," }}

	{{- template "MulByNonResiduePowerFp" dict "all" . "powerNum" 2 "powerName" "Square" "pComment" "^2" "betaDecimal" "80949648264912719408558363140637477264845294720710499478137287262712535938301461879813459410945" "betaArray" "15766275933608376691,\n15635974902606112666,\n1934946774703877852,\n18129354943882397960,\n15437979634065614942,\n101285514078273488," }}

	{{- template "MulByNonResiduePowerFp" dict "all" . "powerNum" 3 "powerName" "Square" "pComment" "^2" "betaDecimal" "258664426012969094010652733694893533536393512754914660539884262666720468348340822774968888139573360124440321458176" "betaArray" "9384023879812382873,\n14252412606051516495,\n9184438906438551565,\n11444845376683159689,\n8738795276227363922,\n81297770384137296," }}

	{{- template "MulByNonResiduePowerFp" dict "all" . "powerNum" 4 "powerName" "Square" "pComment" "^2" "betaDecimal" "258664426012969093929703085429980814127835149614277183275038967946009968870203535512256352201271898244626862047231" "betaArray" "3203870859294639911,\n276961138506029237,\n9479726329337356593,\n13645541738420943632,\n7584832609311778094,\n101110569012358506," }}

	{{- template "MulByNonResiduePowerFp" dict "all" . "powerNum" 5 "powerName" "Square" "pComment" "^2" "betaDecimal" "258664426012969093929703085429980814127835149614277183275038967946009968870203535512256352201271898244626862047232" "betaArray" "12266591053191808654,\n4471292606164064357,\n295287422898805027,\n2200696361737783943,\n17292781406793965788,\n19812798628221209," }}

	{{- template "MulByNonResiduePowerFp" dict "all" . "powerNum" 1 "powerName" "Cube" "pComment" "^3" "betaDecimal" "216465761340224619389371505802605247630151569547285782856803747159100223055385581585702401816380679166954762214499" "betaArray" "10965161018967488287,\n18251363109856037426,\n7036083669251591763,\n16109345360066746489,\n4679973768683352764,\n96952949334633821," }}

	{{- template "MulByNonResiduePowerFp" dict "all" . "powerNum" 2 "powerName" "Cube" "pComment" "^3" "betaDecimal" "258664426012969094010652733694893533536393512754914660539884262666720468348340822774968888139573360124440321458176" "betaArray" "9384023879812382873,\n14252412606051516495,\n9184438906438551565,\n11444845376683159689,\n8738795276227363922,\n81297770384137296," }}

	{{- template "MulByNonResiduePowerFp" dict "all" . "powerNum" 3 "powerName" "Cube" "pComment" "^3" "betaDecimal" "42198664672744474621281227892288285906241943207628877683080515507620245292955241189266486323192680957485559243678" "betaArray" "17067705967832697058,\n1855904398914139597,\n13640894602060642732,\n4220705945553435413,\n9604043198466676350,\n24145363371860877," }}

	{{- template "MulByNonResiduePowerFp" dict "all" . "powerNum" 4 "powerName" "Cube" "pComment" "^3" "betaDecimal" "1" }}
	
	{{- template "MulByNonResiduePowerFp" dict "all" . "powerNum" 5 "powerName" "Cube" "pComment" "^3" "betaDecimal" "216465761340224619389371505802605247630151569547285782856803747159100223055385581585702401816380679166954762214499" "betaArray" "10965161018967488287,\n18251363109856037426,\n7036083669251591763,\n16109345360066746489,\n4679973768683352764,\n96952949334633821," }}

{{- else if and (eq .Fp6NonResidue "1,1") (eq .FpModulus "4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559787") }}

	{{- template "MulByNonResiduePowerFp2" dict "all" . "powerNum" 1 "powerName" "" "pComment" "" "betaDecimal" "3850754370037169011952147076051364057158807420970682438676050522613628423219637725072182697113062777891589506424760" "betaDecimalU" "151655185184498381465642749684540099398075398968325446656007613510403227271200139370504932015952886146304766135027" "betaArray" "506819140503852133,\n14297063575771579155,\n10946065744702939791,\n11771194236670323182,\n2081670087578406477,\n644615147456521963," "betaArrayU" "12895611875574011462,\n6359822009455181036,\n14936352902570693524,\n13914887797453940944,\n3330433690892295817,\n1229183470191017903," }}

	{{- template "MulByNonResiduePowerFp2" dict "all" . "powerNum" 2 "powerName" "" "pComment" "" "betaDecimal" "0" "betaDecimalU" "4002409555221667392624310435006688643935503118305586438271171395842971157480381377015405980053539358417135540939436" "betaArray" "0,\n0,\n0,\n0,\n0,\n0," "betaArrayU" "14772873186050699377,\n6749526151121446354,\n6372666795664677781,\n10283423008382700446,\n286397964926079186,\n1796971870900422465," }}

	{{- template "MulByNonResiduePowerFp2" dict "all" . "powerNum" 3 "powerName" "" "pComment" "" "betaDecimal" "1028732146235106349975324479215795277384839936929757896155643118032610843298655225875571310552543014690878354869257" "betaDecimalU" "1028732146235106349975324479215795277384839936929757896155643118032610843298655225875571310552543014690878354869257" "betaArray" "8921533702591418330,\n15859389534032789116,\n3389114680249073393,\n15116930867080254631,\n3288288975085550621,\n1021049300055853010," "betaArrayU" "8921533702591418330,\n15859389534032789116,\n3389114680249073393,\n15116930867080254631,\n3288288975085550621,\n1021049300055853010," }}

	{{- template "MulByNonResiduePowerFp" dict "all" . "powerNum" 4 "powerName" "" "pComment" "" "betaDecimal" "4002409555221667392624310435006688643935503118305586438271171395842971157480381377015405980053539358417135540939437" "betaArray" "9875771541238924739,\n3094855109658912213,\n5802897354862067244,\n11677019699073781796,\n1505592401347711080,\n1505729768134575418," }}

	{{- template "MulByNonResiduePowerFp2" dict "all" . "powerNum" 5 "powerName" "" "pComment" "" "betaDecimal" "877076961050607968509681729531255177986764537961432449499635504522207616027455086505066378536590128544573588734230" "betaDecimalU" "3125332594171059424908108096204648978570118281977575435832422631601824034463382777937621250592425535493320683825557" "betaArray" "9428352843095270463,\n11709709036094816655,\n14335180424952013185,\n8441381030041026197,\n5369959062663957099,\n1665664447512374973," "betaArrayU" "3974078172982593132,\n8947176549131943536,\n11547238222321620130,\n17244701004083237929,\n42144715806745195,\n208134170135164893," }}

	{{- template "MulByNonResiduePowerFp" dict "all" . "powerNum" 1 "powerName" "Square" "pComment" "^2" "betaDecimal" "793479390729215512621379701633421447060886740281060493010456487427281649075476305620758731620351" "betaArray" "17076301903736715834,\n13907359434105313836,\n1063007777899403918,\n15402659025741563681,\n5125705813544623108,\n76826746747117401," }}

	{{- template "MulByNonResiduePowerFp" dict "all" . "powerNum" 2 "powerName" "Square" "pComment" "^2" "betaDecimal" "793479390729215512621379701633421447060886740281060493010456487427281649075476305620758731620350" "betaArray" "3526659474838938856,\n17562030475567847978,\n1632777218702014455,\n14009062335050482331,\n3906511377122991214,\n368068849512964448," }}

	{{- template "MulByNonResiduePowerFp" dict "all" . "powerNum" 3 "powerName" "Square" "pComment" "^2" "betaDecimal" "4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559786" "betaArray" "4897101644811774638,\n3654671041462534141,\n569769440802610537,\n17053147383018470266,\n17227549637287919721,\n291242102765847046," }}

	{{- template "MulByNonResiduePowerFp" dict "all" . "powerNum" 4 "powerName" "Square" "pComment" "^2" "betaDecimal" "4002409555221667392624310435006688643935503118305586438271171395842971157480381377015405980053539358417135540939436" "betaArray" "14772873186050699377,\n6749526151121446354,\n6372666795664677781,\n10283423008382700446,\n286397964926079186,\n1796971870900422465," }}

	{{- template "MulByNonResiduePowerFp" dict "all" . "powerNum" 5 "powerName" "Square" "pComment" "^2" "betaDecimal" "4002409555221667392624310435006688643935503118305586438271171395842971157480381377015405980053539358417135540939437" "betaArray" "9875771541238924739,\n3094855109658912213,\n5802897354862067244,\n11677019699073781796,\n1505592401347711080,\n1505729768134575418," }}

	{{- template "MulByNonResiduePowerFp2" dict "all" . "powerNum" 1 "powerName" "Cube" "pComment" "^3" "betaDecimal" "2973677408986561043442465346520108879172042883009249989176415018091420807192182638567116318576472649347015917690530" "betaDecimalU" "1028732146235106349975324479215795277384839936929757896155643118032610843298655225875571310552543014690878354869257" "betaArray" "4480897313486445265,\n4797496051193971075,\n4046559893315008306,\n10569151167044009496,\n2123814803385151673,\n852749317591686856," "betaArrayU" "8921533702591418330,\n15859389534032789116,\n3389114680249073393,\n15116930867080254631,\n3288288975085550621,\n1021049300055853010," }}

	{{- template "MulByNonResiduePowerFp2" dict "all" . "powerNum" 2 "powerName" "Cube" "pComment" "^3" "betaDecimal" "0" "betaDecimalU" "1" "betaArray" "0,\n0,\n0,\n0,\n0,\n0," "betaArrayU" "8505329371266088957,\n17002214543764226050,\n6865905132761471162,\n8632934651105793861,\n6631298214892334189,\n1582556514881692819," }}

	{{- template "MulByNonResiduePowerFp2" dict "all" . "powerNum" 3 "powerName" "Cube" "pComment" "^3" "betaDecimal" "2973677408986561043442465346520108879172042883009249989176415018091420807192182638567116318576472649347015917690530" "betaDecimalU" "2973677408986561043442465346520108879172042883009249989176415018091420807192182638567116318576472649347015917690530" "betaArray" "4480897313486445265,\n4797496051193971075,\n4046559893315008306,\n10569151167044009496,\n2123814803385151673,\n852749317591686856," "betaArrayU" "4480897313486445265,\n4797496051193971075,\n4046559893315008306,\n10569151167044009496,\n2123814803385151673,\n852749317591686856," }}

	{{- template "MulByNonResiduePowerFp" dict "all" . "powerNum" 4 "powerName" "Cube" "pComment" "^3" "betaDecimal" "4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559786" "betaArray" "4897101644811774638,\n3654671041462534141,\n569769440802610537,\n17053147383018470266,\n17227549637287919721,\n291242102765847046," }}

	{{- template "MulByNonResiduePowerFp2" dict "all" . "powerNum" 5 "powerName" "Cube" "pComment" "^3" "betaDecimal" "1028732146235106349975324479215795277384839936929757896155643118032610843298655225875571310552543014690878354869257" "betaDecimalU" "2973677408986561043442465346520108879172042883009249989176415018091420807192182638567116318576472649347015917690530" "betaArray" "8921533702591418330,\n15859389534032789116,\n3389114680249073393,\n15116930867080254631,\n3288288975085550621,\n1021049300055853010," "betaArrayU" "4480897313486445265,\n4797496051193971075,\n4046559893315008306,\n10569151167044009496,\n2123814803385151673,\n852749317591686856," }}

{{- else if and (eq .Fp6NonResidue "9,1") (eq .FpModulus "21888242871839275222246405745257275088696311157297823662689037894645226208583") }}
	// MulByNonResiduePower1 set z=x*(9,1)^(1*(p-1)/6) and return z
	func (z *e2) MulByNonResiduePower1(x *e2) *e2 {
		// (9,1)^(1*(p-1)/6)
		// 3850754370037169011952147076051364057158807420970682438676050522613628423219637725072182697113062777891589506424760 + u*151655185184498381465642749684540099398075398968325446656007613510403227271200139370504932015952886146304766135027
		b := e2{
			A0: fp.Element{
				12653890742059813127,
				14585784200204367754,
				1278438861261381767,
				212598772761311868,
			},
			A1: fp.Element{
				11683091849979440498,
				14992204589386555739,
				15866167890766973222,
				1200023580730561873,
			},
		}
		z.Mul(x, &b)
		return z
	}

	// MulByNonResiduePower2 set z=x*(9,1)^(2*(p-1)/6) and return z
	func (z *e2) MulByNonResiduePower2(x *e2) *e2 {
		// (9,1)^(2*(p-1)/6)
		// 0 + u*4002409555221667392624310435006688643935503118305586438271171395842971157480381377015405980053539358417135540939436
		b := e2{
			A0: fp.Element{
				13075984984163199792,
				3782902503040509012,
				8791150885551868305,
				1825854335138010348,
			},
			A1: fp.Element{
				7963664994991228759,
				12257807996192067905,
				13179524609921305146,
				2767831111890561987,
			},
		}
		z.Mul(x, &b)
		return z
	}

	// MulByNonResiduePower3 set z=x*(9,1)^(3*(p-1)/6) and return z
	func (z *e2) MulByNonResiduePower3(x *e2) *e2 {
		// (9,1)^(3*(p-1)/6)
		// 1028732146235106349975324479215795277384839936929757896155643118032610843298655225875571310552543014690878354869257 + u*1028732146235106349975324479215795277384839936929757896155643118032610843298655225875571310552543014690878354869257
		b := e2{
			A0: fp.Element{
				16482010305593259561,
				13488546290961988299,
				3578621962720924518,
				2681173117283399901,
			},
			A1: fp.Element{
				11661927080404088775,
				553939530661941723,
				7860678177968807019,
				3208568454732775116,
			},
		}
		z.Mul(x, &b)
		return z
	}

	// MulByNonResiduePower4 set z=x*(9,1)^(4*(p-1)/6) and return z
	func (z *e2) MulByNonResiduePower4(x *e2) *e2 {
		// (9,1)^(4*(p-1)/6)
		// 4002409555221667392624310435006688643935503118305586438271171395842971157480381377015405980053539358417135540939437
		b := e2{
			A0: fp.Element{
				8314163329781907090,
				11942187022798819835,
				11282677263046157209,
				1576150870752482284,
			},
			A1: fp.Element{
				6763840483288992073,
				7118829427391486816,
				4016233444936635065,
				2630958277570195709,
			},
		}
		z.Mul(x, &b)
		return z
	}

	// MulByNonResiduePower5 set z=x*(9,1)^(5*(p-1)/6) and return z
	func (z *e2) MulByNonResiduePower5(x *e2) *e2 {
		// (9,1)^(5*(p-1)/6)
		// 877076961050607968509681729531255177986764537961432449499635504522207616027455086505066378536590128544573588734230 + u*3125332594171059424908108096204648978570118281977575435832422631601824034463382777937621250592425535493320683825557
		b := e2{
			A0: fp.Element{
				14515217250696892391,
				16303087968080972555,
				3656613296917993960,
				1345095164996126785,
			},
			A1: fp.Element{
				957117326806663081,
				367382125163301975,
				15253872307375509749,
				3396254757538665050,
			},
		}
		z.Mul(x, &b)
		return z
	}

	// MulByNonResiduePowerSquare1 set z=x*(9,1)^(1*(p^2-1)/6) and return z
	func (z *e2) MulByNonResiduePowerSquare1(x *e2) *e2 {
		// (9,1)^(1*(p^2-1)/6)
		// 793479390729215512621379701633421447060886740281060493010456487427281649075476305620758731620351
		b := fp.Element{
			14595462726357228530,
			17349508522658994025,
			1017833795229664280,
			299787779797702374,
		}
		z.A0.Mul(&x.A0, &b)
		z.A1.Mul(&x.A1, &b)
		return z
	}

	// MulByNonResiduePowerSquare2 set z=x*(9,1)^(2*(p^2-1)/6) and return z
	func (z *e2) MulByNonResiduePowerSquare2(x *e2) *e2 {
		// (9,1)^(2*(p^2-1)/6)
		// 793479390729215512621379701633421447060886740281060493010456487427281649075476305620758731620350
		b := fp.Element{
			3697675806616062876,
			9065277094688085689,
			6918009208039626314,
			2775033306905974752,
		}
		z.A0.Mul(&x.A0, &b)
		z.A1.Mul(&x.A1, &b)
		return z
	}

	// MulByNonResiduePowerSquare3 set z=x*(9,1)^(3*(p^2-1)/6) and return z
	func (z *e2) MulByNonResiduePowerSquare3(x *e2) *e2 {
		// (9,1)^(3*(p^2-1)/6)
		// 4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559786
		b := fp.Element{
			7548957153968385962,
			10162512645738643279,
			5900175412809962033,
			2475245527108272378,
		}
		z.A0.Mul(&x.A0, &b)
		z.A1.Mul(&x.A1, &b)
		return z
	}

	// MulByNonResiduePowerSquare4 set z=x*(9,1)^(4*(p^2-1)/6) and return z
	func (z *e2) MulByNonResiduePowerSquare4(x *e2) *e2 {
		// (9,1)^(4*(p^2-1)/6)
		// 4002409555221667392624310435006688643935503118305586438271171395842971157480381377015405980053539358417135540939436
		b := fp.Element{
			8183898218631979349,
			12014359695528440611,
			12263358156045030468,
			3187210487005268291,
		}
		z.A0.Mul(&x.A0, &b)
		z.A1.Mul(&x.A1, &b)
		return z
	}

	// MulByNonResiduePowerSquare5 set z=x*(9,1)^(5*(p^2-1)/6) and return z
	func (z *e2) MulByNonResiduePowerSquare5(x *e2) *e2 {
		// (9,1)^(5*(p^2-1)/6)
		// 4002409555221667392624310435006688643935503118305586438271171395842971157480381377015405980053539358417135540939437
		b := fp.Element{
			634941064663593387,
			1851847049789797332,
			6363182743235068435,
			711964959896995913,
		}
		z.A0.Mul(&x.A0, &b)
		z.A1.Mul(&x.A1, &b)
		return z
	}

	// MulByNonResiduePowerCube1 set z=x*(9,1)^(1*(p^3-1)/6) and return z
	func (z *e2) MulByNonResiduePowerCube1(x *e2) *e2 {
		// (9,1)^(1*(p^3-1)/6)
		// 2973677408986561043442465346520108879172042883009249989176415018091420807192182638567116318576472649347015917690530 + u*1028732146235106349975324479215795277384839936929757896155643118032610843298655225875571310552543014690878354869257
		b := e2{
			A0: fp.Element{
				3914496794763385213,
				790120733010914719,
				7322192392869644725,
				581366264293887267,
			},
			A1: fp.Element{
				12817045492518885689,
				4440270538777280383,
				11178533038884588256,
				2767537931541304486,
			},
		}
		z.Mul(x, &b)
		return z
	}

	// MulByNonResiduePowerCube2 set z=x*(9,1)^(2*(p^3-1)/6) and return z
	func (z *e2) MulByNonResiduePowerCube2(x *e2) *e2 {
		// (9,1)^(2*(p^3-1)/6)
		// 0 + u*1
		b := e2{
			A0: fp.Element{
				14532872967180610477,
				12903226530429559474,
				1868623743233345524,
				2316889217940299650,
			},
			A1: fp.Element{
				12447993766991532972,
				4121872836076202828,
				7630813605053367399,
				740282956577754197,
			},
		}
		z.Mul(x, &b)
		return z
	}

	// MulByNonResiduePowerCube3 set z=x*(9,1)^(3*(p^3-1)/6) and return z
	func (z *e2) MulByNonResiduePowerCube3(x *e2) *e2 {
		// (9,1)^(3*(p^3-1)/6)
		// 2973677408986561043442465346520108879172042883009249989176415018091420807192182638567116318576472649347015917690530 + u*2973677408986561043442465346520108879172042883009249989176415018091420807192182638567116318576472649347015917690530
		b := e2{
			A0: fp.Element{
				6297350639395948318,
				15875321927225446337,
				9702569988553770230,
				805825149519570764,
			},
			A1: fp.Element{
				11117433864585119104,
				10363184613815941297,
				5420513773305887730,
				278429812070195549,
			},
		}
		z.Mul(x, &b)
		return z
	}

	// MulByNonResiduePowerCube4 set z=x*(9,1)^(4*(p^3-1)/6) and return z
	func (z *e2) MulByNonResiduePowerCube4(x *e2) *e2 {
		// (9,1)^(4*(p^3-1)/6)
		// 4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559786
		b := e2{
			A0: fp.Element{
				4938922280314430175,
				13823286637238282975,
				15589480384090068090,
				481952561930628184,
			},
			A1: fp.Element{
				3105754162722846417,
				11647802298615474591,
				13057042392041828081,
				1660844386505564338,
			},
		}
		z.Mul(x, &b)
		return z
	}

	// MulByNonResiduePowerCube5 set z=x*(9,1)^(5*(p^3-1)/6) and return z
	func (z *e2) MulByNonResiduePowerCube5(x *e2) *e2 {
		// (9,1)^(5*(p^3-1)/6)
		// 1028732146235106349975324479215795277384839936929757896155643118032610843298655225875571310552543014690878354869257 + u*2973677408986561043442465346520108879172042883009249989176415018091420807192182638567116318576472649347015917690530
		b := e2{
			A0: fp.Element{
				16193900971494954399,
				13995139551301264911,
				9239559758168096094,
				1571199014989505406,
			},
			A1: fp.Element{
				3254114329011132839,
				11171599147282597747,
				10965492220518093659,
				2657556514797346915,
			},
		}
		z.Mul(x, &b)
		return z
	}
{{- else }}
	// panic("not implemented yet")
{{- end }}
`
