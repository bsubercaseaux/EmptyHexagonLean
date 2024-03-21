function computeStarPolygon(referencePoint, points) {
  // first remove points to the left of referencePoint.
  let filteredPoints = points.filter(p => p.x > referencePoint.x);
  // now sort by angle with respect to referencePoint.
  let sortedPoints = filteredPoints.sort((p1, p2) => {
    let angleP1 = Math.atan2(p1.y - referencePoint.y, p1.x - referencePoint.x);
    let angleP2 = Math.atan2(p2.y - referencePoint.y, p2.x - referencePoint.x);
    return angleP1 - angleP2;
  });
  return {
    pointSequence: [referencePoint, ...sortedPoints],
    referencePoint: referencePoint
  };
};

function ccw(a, b, c) {
  return (b.x - a.x) * (c.y - a.y) - (c.x - a.x) * (b.y - a.y) > 0;
}

function proceed(starPolygon, i, j, queues, answer) {
  let Q_i = queues[i];
  let Q_j = queues[j];
  // is Q_i[0] -> i -> j ccw?

  while (Q_i.length > 0) {
    let ccw_ij = ccw(starPolygon.pointSequence[Q_i[0]],
      starPolygon.pointSequence[i],
      starPolygon.pointSequence[j]);
    if (!ccw_ij) {
      break;
    }
    proceed(starPolygon, Q_i[0], j, queues, answer);
    Q_i.shift();
  }
  answer.push([i, j]);
  Q_j.push(i);
}


function chainTreat(visibilityGraph, p, Lmap, ChMap, r, answerChains) {
  let S_i = visibilityGraph.edges.filter(edge => edge[1] === p);
  let S_o = visibilityGraph.edges.filter(edge => edge[0] === p);
  let S_o_sorted = S_o.sort((edge1, edge2) => Lmap[edge2] - Lmap[edge1]);
  for (let j = 0; j < S_o.length; ++j) {
    //console.log("S_o[j]", S_o[j], "Lmap[S_o[j]]", Lmap[S_o[j]], "r-2", r-2);
    if (Lmap[S_o[j]] >= r - 2) {
      // console.log("value is >= r-2", (r-2));
      ChMap[S_o[j]] = [[S_o[j]]];
    } else {
      ChMap[S_o[j]] = [];
    }
  }

  let m = 0;
  let om = S_o.length - 1;
  for (let j = 0; j < S_i.length; ++j) {
    while (m <= S_o.length - 1) {
      let ccw_jm = ccw(visibilityGraph.pointSequence[S_i[j][0]],
        visibilityGraph.pointSequence[S_i[j][1]],
        visibilityGraph.pointSequence[S_o[m][1]]);
      if (ccw_jm) {
        break;
      }
      S_o_sorted = S_o_sorted.filter(edge => edge !== S_o[m]);
      om -= 1;
      m += 1;
    }
    ChMap[S_i[j]].forEach(chain => {
      let t = 0;
      let l = chain.length;
      while (t <= om && Lmap[S_o_sorted[t]] >= r - 2 - l) {
        chain.push(S_o_sorted[t]);
        if (l === r - 3) {
          // console.log("Found empty convex polygon of desired length!!");
          // console.log("l", l, " chain length: ", chain.length, " chain: ", chain);
          answerChains.push(chain);
        } else {
          ChMap[S_o_sorted[t]].push(chain);
        }
        t += 1;
      }
    });
  }
}

function chainTreatment(visibilityGraph, Lmap, ChMap, r, answerChains) {
  for (let i = 0; i < visibilityGraph.pointSequence.length - 1; ++i) {
    chainTreat(visibilityGraph, i, Lmap, ChMap, r, answerChains);
  }
  return ChMap;
}

function maxChainTreat(visibilityGraph, p, Lmap) {
  let pIncoming = visibilityGraph.edges.filter(edge => edge[1] === p);
  let pOutgoing = visibilityGraph.edges.filter(edge => edge[0] === p);
  let l = pOutgoing.length - 1;
  let m = 0;
  for (let j = pIncoming.length - 1; j >= 0; --j) {
    Lmap[pIncoming[j]] = m + 1;
    while (l >= 0) {
      let ccw_jl = ccw(visibilityGraph.pointSequence[pIncoming[j][0]],
        visibilityGraph.pointSequence[pIncoming[j][1]],
        visibilityGraph.pointSequence[pOutgoing[l][1]]);
      if (!ccw_jl) {
        break;
      }
      if (Lmap[pOutgoing[l]] > m) {
        m = Lmap[pOutgoing[l]];
        Lmap[pIncoming[j]] = m + 1;
      }
      l -= 1;
    }
  }
}

function maxChain(visibilityGraph, Lmap) {
  for (let i = visibilityGraph.pointSequence.length - 1; i >= 0; --i) {
    maxChainTreat(visibilityGraph, i, Lmap);
  }
}

function computeVisibilityGraph(starPolygon) {
  let queues = [];
  let answer = [];
  for (let i = 0; i < starPolygon.pointSequence.length; i++) {
    queues.push([]);
  }
  for (let i = 0; i < starPolygon.pointSequence.length - 1; i++) {
    proceed(starPolygon, i, i + 1, queues, answer);
  }
  // discard edges including point p.
  answer = answer.filter(edge => edge[0] !== 0 && edge[1] !== 0);
  return {
    pointSequence: starPolygon.pointSequence,
    referencePoint: starPolygon.referencePoint,
    edges: answer
  };
}

function computeHoles(allPoints, r) {
  let holes = [];
  for (let idP = 0; idP < allPoints.length; idP++) {
    let p = allPoints[idP];
    let starPolygon = computeStarPolygon(p, allPoints);
    let pGraph = computeVisibilityGraph(starPolygon);
    let Lmap = {};
    maxChain(pGraph, Lmap);
    let ChMap = {};
    let answerChains = [];
    chainTreatment(pGraph, Lmap, ChMap, r, answerChains);
    for (let i = 0; i < answerChains.length; i++) {
      let hole = [pGraph.pointSequence[0]];
      for (let j = 0; j < answerChains[i].length; j++) {
        if (j === 0) {
          hole.push(pGraph.pointSequence[answerChains[i][j][0]]);
          hole.push(pGraph.pointSequence[answerChains[i][j][1]]);
        } else {
          hole.push(pGraph.pointSequence[answerChains[i][j][1]]);
        }
      }
      holes.push(hole);
    }
  }
  //console.log(holes);
  return holes;
}

const points = [
  [1, 1260],
  [16, 743],
  [22, 531],
  [37, 0],
  [306, 592],
  [310, 531],
  [366, 552],
  [371, 487],
  [374, 525],
  [392, 575],
  [396, 613],
  [410, 539],
  [416, 550],
  [426, 526],
  [434, 552],
  [436, 535],
  [446, 565],
  [449, 518],
  [450, 498],
  [453, 542],
  [458, 526],
  [489, 537],
  [492, 502],
  [496, 579],
  [516, 467],
  [552, 502],
  [754, 697],
  [777, 194],
  [1259, 320],
];
const k = 6;
const result = computeHoles(points.map(p => ({ x: p[0], y: p[1] })), k);
console.log(result);
