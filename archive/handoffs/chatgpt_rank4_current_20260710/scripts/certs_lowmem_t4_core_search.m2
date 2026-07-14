-- Ordinary-GB equation-core search for the two t4 targets that first close at
-- degree 6.  This script never asks for ChangeMatrix.  It loads the validated
-- direct-triple generator builder, quotients the linear axioms, removes exact
-- duplicate images, and greedily deletes blocks while retaining membership.
--
-- Scan:
--   CERT_BRANCH=t4 CERT_MODE=build CORE_MODE=scan M2 --script \
--       scripts/certs_lowmem_t4_core_search.m2
-- Search one target (run targets 4 and 7 in separate processes):
--   CERT_BRANCH=t4 CERT_MODE=build CORE_MODE=search CORE_TARGET=4 M2 --script \
--       scripts/certs_lowmem_t4_core_search.m2

load "scripts/certs_lowmem.m2";
assert(branch == "t4");

linPosC = select(toList(0..#gensList-1),
    i -> first degree(gensList#i) == 1);
nonPosC = select(toList(0..#gensList-1),
    i -> not member(i,linPosC));
linListC = apply(linPosC,i -> gensList#i);
TC = Q/(ideal linListC);
SC = prune TC;
rhoC = TC.minimalPresentationMap * map(TC,Q);

rawPairsC = select(apply(nonPosC,i -> {i,rhoC(gensList#i)}),p -> p#1 != 0);
seenC = new MutableHashTable;
pairsC = {};
for p in rawPairsC do if not seenC#?(p#1) then (
    seenC#(p#1) = #pairsC;
    pairsC = append(pairsC,p));
redPosC = apply(pairsC,p -> p#0);
redListC = apply(pairsC,p -> p#1);

<< "CORE SETUP t4: linear=" << #linPosC
   << " variables=" << numgens Q << "->" << numgens SC
   << " rawReduced=" << #rawPairsC << " dedupReduced=" << #redListC
   << endl << flush;

testCore = (core,targetIndex,d) -> (
    M := matrix{apply(core,j -> redListC#j)};
    Gc := gb(M,DegreeLimit=>d,HardDegreeLimit=>d);
    ok := matrix{{rhoC(bQ#targetIndex)}} % Gc == 0;
    unit := 1_SC % Gc == 0;
    Gc = null;
    gbRemove M;
    M = null;
    collectGarbage();
    assert(not unit);
    ok);

writeCheckpoint = (targetIndex,core,tag) -> (
    fnc := "scripts/certs_lowmem_t4_core_target" | toString targetIndex
        | "_20260710.m2data";
    tmpc := fnc | ".part";
    if fileExists tmpc then removeFile tmpc;
    fhc := openOut tmpc;
    fhc << "-- target " << targetIndex << " "
        << (data#"targetLabels")#targetIndex << endl;
    fhc << "-- checkpoint " << tag << endl;
    fhc << "coreReducedIndices = " << toExternalString core << endl;
    fhc << "coreOriginalGeneratorIndices = "
        << toExternalString apply(core,j -> redPosC#j) << endl;
    close fhc;
    moveFile(tmpc,fnc));

coreMode = getenv "CORE_MODE";
if coreMode === null then coreMode = "scan";

if coreMode == "scan" then (
    allCore := toList(0..#redListC-1);
    scanRows := {};
    << "TARGET LABELS " << apply(toList(0..#bQ-1),
        i -> (i,(data#"targetLabels")#i)) << endl << flush;
    for d in {2,3,4,5} do (
        Mc := matrix{redListC};
        Gc := gb(Mc,DegreeLimit=>d,HardDegreeLimit=>d);
        openC := select(toList(0..#bQ-1),
            i -> matrix{{rhoC(bQ#i)}} % Gc != 0);
        << "PRUNED SCAN t4 degree " << d << " open=" << openC
           << endl << flush;
        scanRows = append(scanRows,(d,openC));
        Gc = null;
        gbRemove Mc;
        Mc = null;
        collectGarbage());
    scanFn := "scripts/certs_lowmem_t4_pruned_scan_20260710.m2data";
    scanPart := scanFn | ".part";
    if fileExists scanPart then removeFile scanPart;
    scanFh := openOut scanPart;
    scanFh << "linearOriginalGeneratorIndices = "
        << toExternalString linPosC << endl;
    scanFh << "variableCountOriginal = " << numgens Q << endl;
    scanFh << "variableCountPruned = " << numgens SC << endl;
    scanFh << "rawReducedGeneratorCount = " << #rawPairsC << endl;
    scanFh << "dedupReducedGeneratorCount = " << #redListC << endl;
    scanFh << "reducedRepresentativeOriginalGeneratorIndices = "
        << toExternalString redPosC << endl;
    scanFh << "targetLabels = "
        << toExternalString(data#"targetLabels") << endl;
    scanFh << "openTargetIndicesByDegree = "
        << toExternalString scanRows << endl;
    close scanFh;
    moveFile(scanPart,scanFn);
    << "PRUNED SCAN ARTIFACT " << scanFn << endl << flush;
) else if coreMode == "search" then (
    targetString := getenv "CORE_TARGET";
    if targetString === null then error "CORE_TARGET=4 or 7 is required";
    targetIndex := value targetString;
    if not member(targetIndex,{4,7}) then error "CORE_TARGET must be 4 or 7";
    core := toList(0..#redListC-1);
    << "CORE INITIAL TEST target=" << targetIndex << " "
       << (data#"targetLabels")#targetIndex << " size=" << #core << flush;
    elapsedTime ok0 := testCore(core,targetIndex,6);
    << " result=" << ok0 << endl << flush;
    assert ok0;
    writeCheckpoint(targetIndex,core,"initial");
    trial := 0;
    for blockSize in {64,32,16,8,4,2,1} do (
        pos := 0;
        while pos < #core do (
            lastPos := min(#core-1,pos+blockSize-1);
            block := for u from pos to lastPos list core#u;
            candidate := select(core,j -> not member(j,block));
            if #candidate == 0 then (
                pos = lastPos+1;
            ) else (
                trial = trial+1;
                << "CORE TRIAL " << trial << " target=" << targetIndex
                   << " block=" << blockSize << " size " << #core
                   << "->" << #candidate << flush;
                elapsedTime ok := testCore(candidate,targetIndex,6);
                << " result=" << ok << endl << flush;
                if ok then (
                    core = candidate;
                    writeCheckpoint(targetIndex,core,
                        "accepted-trial-" | toString trial);
                ) else pos = lastPos+1));
        << "CORE PASS target=" << targetIndex << " block=" << blockSize
           << " size=" << #core << endl << flush;);
    assert testCore(core,targetIndex,6);
    writeCheckpoint(targetIndex,core,"complete");
    << "CORE COMPLETE target=" << targetIndex << " size=" << #core
       << " reducedIndices=" << core << endl;
    << "CORE ORIGINAL GENERATOR INDICES="
       << apply(core,j -> redPosC#j) << endl << flush;
) else error "CORE_MODE must be scan or search";
