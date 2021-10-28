import subprocess
from os import listdir
import sys

if len(sys.argv) != 3:
	print(f"Usage: python {sys.argv[0]} /path/to/instances timeout")
	exit(1)

instances = listdir(sys.argv[1])
num_instances = len(instances)
timeout = int(sys.argv[2])

print("name, mode, nodes, edges, maxdeg, mindeg, preproc-reduction, success")

for instance in instances:
	for mode in ["-p", "-d", "-i"]:
		try:
			command = ["cargo", "run", "--release", "--quiet", "--", "--file", f"{sys.argv[1]}/{instance}", "-c", mode]
			p = subprocess.run(command, stdout=subprocess.PIPE, encoding="UTF-8", timeout=timeout)
			if p.returncode == 0:
				print(f"{instance}, {mode}, {p.stdout.strip()}, 0")
			else:
				print(f"{instance}, {mode}, {p.stdout.strip()}, 1")
		except subprocess.TimeoutExpired as exc:
			if exc.stdout:
				print(f"{instance}, {mode}, {exc.stdout.strip()}, 2")
			else:
				print(f"{instance}, {mode}, -1, -1, -1, -1, -1")
	sys.stdout.flush()
