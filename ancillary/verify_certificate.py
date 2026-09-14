#!/usr/bin/env python3
"""Independent verifier for the finite certificate of `D_507(23) = 2`.

This is the ancillary program of Appendix A of

    Filippo Cavallari, *Coupling defects of large-prime fibres in optimal path
    partitions of the divisor graph*.

It is deliberately self-contained: it imports **only the Python standard
library**, it invokes **no optimisation routine**, and it reconstructs every
graph from `(N, q)` alone, so the data file cannot smuggle in a different
instance.

What it checks
--------------

For each of the three blocks

    H_507        = divisor graph on {2, ..., 507},
    R_{507,23}   = H_507 minus the multiples of 23,
    G_22         = divisor graph on {1, ..., 22},

the data file supplies

* an explicit **path partition**, which exhibits a spanning linear forest with
  `|V| - k` edges and therefore proves `lambda >= |V| - k`;
* a nonnegative integer **triangle-free 2-matching dual**: weights `Y_v` on
  vertices, `Z_T` on divisor triangles and `W_e` on edges satisfying

      Y_u + Y_v + sum_{T contains e} Z_T + W_e >= 2   for every edge e = uv,

  whose objective `U = 2 sum Y + 2 sum Z + sum W` proves
  `lambda <= floor(U/2)`.  The implication uses only valid inequalities for
  linear forests: `deg_L(v) <= 2`, and an acyclic `L` never contains all three
  edges of a triangle.

The two bounds coincide for each block, so `lambda` is pinned exactly and

    D_507(23) = lambda(H_507) - lambda(R_{507,23}) - lambda(G_22).

The file also carries the constructive witness of Appendix A.3: a partition `M`
of `R_{507,23}` into 100 paths, a partition `J` of `G_22` into 4 paths, and the
three crossings `{12,276}`, `{15,345}`, `{16,368}`.  The verifier checks the
endpoint configuration, the degree bound and the acyclicity of the assembled
forest, and the resulting path count and net saving.

Usage
-----

    python3 ancillary/verify_certificate.py [path/to/defect_507_23.json]

Exit status is 0 when every check passes and 1 otherwise.
"""

from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import Any, Iterator, Mapping, Sequence

SCHEMA_VERSION = 1
CERTIFICATE_TYPE = "induced-triangle-free-2-matching-dual-plus-path-witness"
BLOCK_NAMES = ("ambient", "complement", "fibre")
DEFAULT_DATA = Path(__file__).resolve().parent / "defect_507_23.json"


class CertificateError(Exception):
    """A check failed; the certificate is rejected."""


# --------------------------------------------------------------------------
# JSON loading, with duplicate keys rejected
# --------------------------------------------------------------------------


def _no_duplicate_keys(pairs: Sequence[tuple[str, Any]]) -> dict[str, Any]:
    seen: dict[str, Any] = {}
    for key, value in pairs:
        if key in seen:
            raise CertificateError(f"duplicate JSON key {key!r}")
        seen[key] = value
    return seen


def load(path: Path) -> dict[str, Any]:
    """Parse and return the certificate payload."""
    raw = path.read_bytes()
    try:
        payload = json.loads(raw.decode("utf-8"), object_pairs_hook=_no_duplicate_keys)
    except json.JSONDecodeError as exc:  # pragma: no cover - malformed input
        raise CertificateError(f"{path} is not valid JSON: {exc}") from None
    if not isinstance(payload, dict):
        raise CertificateError("the certificate must be a JSON object")
    return payload


# --------------------------------------------------------------------------
# The graphs, rebuilt from (N, q)
# --------------------------------------------------------------------------


def _is_int(value: object) -> bool:
    return isinstance(value, int) and not isinstance(value, bool)


def _is_prime(value: int) -> bool:
    if value < 2:
        return False
    divisor = 2
    while divisor * divisor <= value:
        if value % divisor == 0:
            return False
        divisor += 1
    return True


def block_vertices(name: str, n: int, q: int) -> list[int]:
    """The vertex set of a block, rebuilt from `(N, q)` alone."""
    if name == "ambient":
        return list(range(2, n + 1))
    if name == "complement":
        return [v for v in range(2, n + 1) if v % q]
    if name == "fibre":
        return list(range(1, n // q + 1))
    raise CertificateError(f"unknown block {name!r}")


def induced_edges(vertices: Sequence[int]) -> Iterator[tuple[int, int]]:
    """Every edge of the divisor graph induced on `vertices`, ascending."""
    present = set(vertices)
    top = max(vertices)
    for small in sorted(vertices):
        large = 2 * small
        while large <= top:
            if large in present:
                yield small, large
            large += small


# --------------------------------------------------------------------------
# Path partitions
# --------------------------------------------------------------------------


def verify_path_partition(vertices: Sequence[int], raw: object, label: str) -> int:
    """Check a path partition of `vertices` and return the number of paths."""
    if not isinstance(raw, list):
        raise CertificateError(f"{label}: path partition must be a list of paths")
    seen: list[int] = []
    for path in raw:
        if not isinstance(path, list) or not path:
            raise CertificateError(f"{label}: path {path!r} must be a non-empty list")
        if not all(_is_int(v) for v in path):
            raise CertificateError(f"{label}: path {path!r} must be integral")
        for left, right in zip(path, path[1:]):
            if left == right or (left % right and right % left):
                raise CertificateError(
                    f"{label}: {left}-{right} is not a divisor-graph edge"
                )
        seen.extend(int(v) for v in path)
    if sorted(seen) != sorted(vertices):
        raise CertificateError(
            f"{label}: the paths do not partition the block's vertex set"
        )
    return len(raw)


# --------------------------------------------------------------------------
# The integer dual
# --------------------------------------------------------------------------


def _weights(raw: object, arity: int, label: str) -> dict[tuple[int, ...], int]:
    out: dict[tuple[int, ...], int] = {}
    if raw is None:
        return out
    if not isinstance(raw, list):
        raise CertificateError(f"{label} must be a list")
    for entry in raw:
        if not isinstance(entry, list) or len(entry) != arity + 1:
            raise CertificateError(f"{label} entry {entry!r} needs {arity + 1} integers")
        if not all(_is_int(value) for value in entry):
            raise CertificateError(f"{label} entry {entry!r} must be integral")
        key = tuple(int(value) for value in entry[:arity])
        weight = int(entry[arity])
        if weight <= 0:
            raise CertificateError(f"{label} weight for {key} must be positive")
        if key in out:
            raise CertificateError(f"{label} lists {key} twice")
        out[key] = weight
    return out


def verify_dual(vertices: Sequence[int], raw: object, label: str) -> int:
    """Check the dual and return the upper bound `floor(objective_twice/2)`."""
    if not isinstance(raw, dict):
        raise CertificateError(f"{label}: dual must be an object")
    present = set(vertices)
    vertex_weights = _weights(raw.get("vertex_weights"), 1, f"{label}.vertex_weights")
    triangle_weights = _weights(raw.get("triangle_weights"), 3, f"{label}.triangle_weights")
    edge_weights = _weights(raw.get("edge_weights"), 2, f"{label}.edge_weights")

    for (vertex,) in vertex_weights:
        if vertex not in present:
            raise CertificateError(f"{label}: vertex weight on {vertex}, outside the block")

    triangle_by_edge: dict[tuple[int, int], int] = {}
    for triangle, weight in triangle_weights.items():
        first, middle, last = triangle
        if not (first in present and middle in present and last in present):
            raise CertificateError(f"{label}: triangle {triangle} leaves the block")
        if first >= middle or middle >= last or middle % first or last % middle:
            raise CertificateError(f"{label}: {triangle} is not a divisor-graph triangle")
        for edge in ((first, middle), (middle, last), (first, last)):
            triangle_by_edge[edge] = triangle_by_edge.get(edge, 0) + weight

    for left, right in edge_weights:
        if left >= right or right % left or left not in present or right not in present:
            raise CertificateError(f"{label}: {(left, right)} is not an edge of the block")

    for left, right in induced_edges(vertices):
        coverage = (
            vertex_weights.get((left,), 0)
            + vertex_weights.get((right,), 0)
            + triangle_by_edge.get((left, right), 0)
            + edge_weights.get((left, right), 0)
        )
        if coverage < 2:
            raise CertificateError(
                f"{label}: dual coverage of edge {left}-{right} is {coverage}, below 2"
            )

    objective_twice = raw.get("objective_twice")
    recomputed = (
        2 * sum(vertex_weights.values())
        + 2 * sum(triangle_weights.values())
        + sum(edge_weights.values())
    )
    if not _is_int(objective_twice) or objective_twice < 0:
        raise CertificateError(f"{label}: objective_twice must be a nonnegative integer")
    if objective_twice != recomputed:
        raise CertificateError(
            f"{label}: objective_twice is {objective_twice}, recomputed {recomputed}"
        )
    return objective_twice // 2


# --------------------------------------------------------------------------
# The constructive witness of Appendix A.3
# --------------------------------------------------------------------------


def verify_collapse(
    raw: object, n: int, q: int, certified: Mapping[str, int]
) -> tuple[int, int, int, int]:
    """Check the constructive witness.

    Returns `(ports, edges_M, edges_J, saving)` where `saving` is the net number
    of paths saved, `|X| - a - b` in the notation of Lemma 2.9.
    """
    if not isinstance(raw, dict):
        raise CertificateError("composite_collapse must be an object")
    ports = raw.get("ports")
    if not isinstance(ports, list) or not ports or not all(_is_int(p) for p in ports):
        raise CertificateError("composite_collapse.ports must be a non-empty integer list")
    ports = [int(p) for p in ports]
    fibre_type = n // q
    if len(set(ports)) != len(ports) or any(not 2 <= p <= fibre_type for p in ports):
        raise CertificateError("composite_collapse.ports must be distinct ports in 2..s")

    edges: list[tuple[int, int]] = []
    side_edges: dict[str, int] = {}
    for name, key in (("complement", "complement_forest"), ("fibre", "fibre_forest")):
        vertices = block_vertices(name, n, q)
        paths = verify_path_partition(vertices, raw.get(key), f"composite_collapse.{key}")
        degrees: dict[int, int] = {}
        for path in raw[key]:
            for left, right in zip(path, path[1:]):
                degrees[left] = degrees.get(left, 0) + 1
                degrees[right] = degrees.get(right, 0) + 1
                edges.append(
                    (int(left), int(right))
                    if name == "complement"
                    else (int(left) * q, int(right) * q)
                )
        for port in ports:
            # `port` names the vertex `c` in the complement and the vertex `c`
            # of `G_s` whose scaled copy is `cq`; in both blocks the crossing
            # `c - cq` needs a free incidence slot there.
            if degrees.get(port, 0) > 1:
                raise CertificateError(
                    f"composite_collapse: the {name} forest has degree "
                    f"{degrees[port]} at port {port}; a crossing needs a free slot"
                )
        side_edges[name] = len(vertices) - paths

    # the diagonal crossings c - cq
    edges.extend((port, port * q) for port in ports)

    degree: dict[int, int] = {}
    parent: dict[int, int] = {}

    def find(x: int) -> int:
        parent.setdefault(x, x)
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    for left, right in edges:
        degree[left] = degree.get(left, 0) + 1
        degree[right] = degree.get(right, 0) + 1
        if degree[left] > 2 or degree[right] > 2:
            raise CertificateError(
                f"composite_collapse: assembled degree above two at {left}-{right}"
            )
        root_left, root_right = find(left), find(right)
        if root_left == root_right:
            raise CertificateError(
                f"composite_collapse: the assembly has a cycle through {left}-{right}"
            )
        parent[root_left] = root_right

    price_complement = certified["complement"] - side_edges["complement"]
    price_fibre = certified["fibre"] - side_edges["fibre"]
    saving = len(ports) - price_complement - price_fibre
    claimed = raw.get("forced_defect")
    if _is_int(claimed) and claimed != saving:
        raise CertificateError(
            f"composite_collapse claims a saving of {claimed}, certifies {saving}"
        )
    return len(ports), side_edges["complement"], side_edges["fibre"], saving


# --------------------------------------------------------------------------
# Top level
# --------------------------------------------------------------------------


def verify(payload: Mapping[str, Any]) -> dict[str, Any]:
    """Check the whole certificate and return the values it proves."""
    if payload.get("schema_version") != SCHEMA_VERSION:
        raise CertificateError("unsupported schema_version")
    if payload.get("certificate_type") != CERTIFICATE_TYPE:
        raise CertificateError("unsupported certificate_type")

    n, q = payload.get("n"), payload.get("q")
    if not _is_int(n) or not _is_int(q) or n < 4 or q < 2:
        raise CertificateError("n and q must be integers with n >= 4 and q >= 2")
    if q * q <= n:
        raise CertificateError(f"q={q} is not a large prime for N={n}")
    if not _is_prime(q):
        raise CertificateError(f"q={q} is not prime")
    fibre_type = n // q
    claimed_type = payload.get("fibre_type")
    if _is_int(claimed_type) and claimed_type != fibre_type:
        raise CertificateError(
            f"fibre_type is {claimed_type}, but floor({n}/{q}) = {fibre_type}"
        )

    ranks: dict[str, int] = {}
    paths: dict[str, int] = {}
    sizes: dict[str, int] = {}
    for name in BLOCK_NAMES:
        block = payload.get(name)
        if not isinstance(block, dict):
            raise CertificateError(f"block {name} must be an object")
        vertices = block_vertices(name, n, q)
        count = verify_path_partition(vertices, block.get("path_partition"), name)
        lower = len(vertices) - count
        upper = verify_dual(vertices, block.get("dual"), name)
        if lower != upper:
            raise CertificateError(
                f"{name}: the witness proves lambda >= {lower} and the dual "
                f"lambda <= {upper}; the certificate does not pin the value"
            )
        claimed = block.get("lambda")
        if _is_int(claimed) and claimed != lower:
            raise CertificateError(f"{name}: claimed lambda={claimed}, certified {lower}")
        ranks[name] = lower
        paths[name] = count
        sizes[name] = len(vertices)

    defect = ranks["ambient"] - ranks["complement"] - ranks["fibre"]
    by_paths = paths["complement"] + paths["fibre"] - paths["ambient"]
    if defect != by_paths:
        raise CertificateError(
            f"the rank form gives {defect} and the path form {by_paths}"
        )
    claimed = payload.get("defect")
    if _is_int(claimed) and claimed != defect:
        raise CertificateError(f"claimed defect {claimed}, certified {defect}")

    crossings, edges_m, edges_j, saving = verify_collapse(
        payload.get("composite_collapse"), n, q, ranks
    )
    if saving > defect:
        raise CertificateError(
            f"the constructive witness forces {saving}, above the certified {defect}"
        )

    return {
        "n": n,
        "q": q,
        "fibre_type": fibre_type,
        "sizes": sizes,
        "ranks": ranks,
        "paths": paths,
        "defect": defect,
        "crossings": crossings,
        "edges_M": edges_m,
        "edges_J": edges_j,
        "assembled_edges": edges_m + edges_j + crossings,
        "assembled_paths": sizes["ambient"] - (edges_m + edges_j + crossings),
        "saving": saving,
    }


def report(result: Mapping[str, Any]) -> str:
    lines = [
        f"instance                 N = {result['n']}, q = {result['q']}, "
        f"s = {result['fibre_type']}",
        "",
        f"{'block':<14}{'|V|':>6}{'paths':>8}{'lambda':>9}",
        f"{'H_N':<14}{result['sizes']['ambient']:>6}"
        f"{result['paths']['ambient']:>8}{result['ranks']['ambient']:>9}",
        f"{'R_{N,q}':<14}{result['sizes']['complement']:>6}"
        f"{result['paths']['complement']:>8}{result['ranks']['complement']:>9}",
        f"{'G_s':<14}{result['sizes']['fibre']:>6}"
        f"{result['paths']['fibre']:>8}{result['ranks']['fibre']:>9}",
        "",
        f"constructive witness     |E(M)| = {result['edges_M']}, "
        f"|E(J)| = {result['edges_J']}, {result['crossings']} crossings",
        f"assembled forest         {result['assembled_edges']} edges, "
        f"{result['assembled_paths']} paths, net saving {result['saving']}",
        f"coupling defect          D_{result['n']}({result['q']}) = {result['defect']}",
    ]
    return "\n".join(lines)


def main(argv: Sequence[str]) -> int:
    path = Path(argv[1]) if len(argv) > 1 else DEFAULT_DATA
    try:
        payload = load(path)
        result = verify(payload)
    except CertificateError as exc:
        print(f"REJECTED: {exc}", file=sys.stderr)
        return 1
    except OSError as exc:
        print(f"REJECTED: cannot read {path}: {exc}", file=sys.stderr)
        return 1
    print(report(result))
    print("\nACCEPTED: every check passed.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))