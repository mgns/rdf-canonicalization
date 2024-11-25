from rdflib import Graph

# Load RDF graph from file
g = Graph()
g.parse("order-1.nt")

print(len(g))

import pprint

#for stmt in g:
#    pprint.pprint(stmt)

# Serialize the RDF graph to a normalized N-Triples format
g.serialize(format="nt", encoding="utf-8", destination="tmp/normalized_nt.nt")

# newline character shall be "\n"
newline = "\n"

line: str
with open("tmp/normalized_nt-sort.nt", "wb") as f:
    for line in sorted(g.serialize(format='nt').splitlines()):
        if line:
            line = line + newline
            f.write(line.encode(encoding="utf-8", errors='strict'))




# Save the normalized RDF graph to a file
# with open("tmp/normalized_nt-sort.nt", "wb") as f:
#    f.write(normalized_graph)
