export { };
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
const r = 6;

type point = { x: number, y: number };
const allPoints: point[] = points.map(p => ({ x: p[0], y: p[1] }));
for (let idP = 0; idP < allPoints.length; idP++) {
  const referencePoint = allPoints[idP];

  const ccw = (a: point, b: point, c: point) =>
    (b.x - a.x) * (c.y - a.y) - (c.x - a.x) * (b.y - a.y) > 0;

  // computeStarPolygon
  // first remove points to the left of referencePoint.
  const filteredPoints = allPoints.filter(p => p.x > referencePoint.x);
  // now sort by angle with respect to referencePoint.
  const sortedPoints = filteredPoints.sort((p1, p2) => {
    let angleP1 = Math.atan2(p1.y - referencePoint.y, p1.x - referencePoint.x);
    let angleP2 = Math.atan2(p2.y - referencePoint.y, p2.x - referencePoint.x);
    return angleP1 - angleP2;
  });
  const pointSequence = [referencePoint, ...sortedPoints];

  // computeVisibilityGraph
  let edges: number[][] = [];
  let queues: number[][] = pointSequence.map(() => []);
  for (let i = 0; i < pointSequence.length - 1; i++) {
    const proceed = function (i: number, j: number) {
      let Q_i = queues[i];
      let Q_j = queues[j];
      // is Q_i[0] -> i -> j ccw?

      while (Q_i.length > 0) {
        let ccw_ij = ccw(
          pointSequence[Q_i[0]],
          pointSequence[i],
          pointSequence[j]);
        if (!ccw_ij) {
          break;
        }
        proceed(Q_i[0], j);
        Q_i.shift();
      }
      // discard edges including point p.
      if (i != 0) edges.push([i, j]);
      Q_j.push(i);
    }
    proceed(i, i + 1);
  }

  // maxChain
  let Lmap: { [index: string]: number[] } = {};
  for (let i = pointSequence.length - 1; i >= 0; --i) {
    let pIncoming = edges.filter(edge => edge[1] === i);
    let pOutgoing = edges.filter(edge => edge[0] === i);
    let l = pOutgoing.length - 1;
    let m: number[] = [i];
    for (let j = pIncoming.length - 1; j >= 0; --j) {
      Lmap[String(pIncoming[j])] = [pIncoming[j][0], ...m];
      while (l >= 0) {
        let ccw_jl = ccw(
          pointSequence[pIncoming[j][0]],
          pointSequence[pIncoming[j][1]],
          pointSequence[pOutgoing[l][1]]);
        if (!ccw_jl) {
          break;
        }
        if (Lmap[String(pOutgoing[l])].length > m.length) {
          m = Lmap[String(pOutgoing[l])];
          const n = [pIncoming[j][0], ...m];
          Lmap[String(pIncoming[j])] = n;
          if (m.length >= r - 2) {
            console.log(`Found empty convex polygon: ${idP}:${n}`);
          }
        }
        l -= 1;
      }
    }
  }
  // console.log(Lmap)
}
