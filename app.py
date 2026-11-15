
from flask import Flask, render_template, request, redirect, url_for, flash, jsonify
from datetime import datetime, timedelta
from collections import deque
import heapq, json, random

app = Flask(__name__)
app.secret_key = "replace-this-with-a-random-secret-key"

# -------------------- Sample farm data --------------------
FARMS = [
    {"id":"SC1001","farmer":"Ramesh Patil","village":"Sameerwadi","area":3.5,"crop_stage":"Grand Growth","moisture":18,"temperature":34,"rainfall":0,"water_need":42,"lat":16.25,"lon":75.12,"last_irrigated":"2026-11-06","electricity":"Available"},
    {"id":"SC1002","farmer":"Savita Kulkarni","village":"Mudhol","area":2.0,"crop_stage":"Tillering","moisture":31,"temperature":30,"rainfall":4,"water_need":18,"lat":16.34,"lon":75.28,"last_irrigated":"2026-11-07","electricity":"Available"},
    {"id":"SC1003","farmer":"Mahesh Naik","village":"Jamkhandi","area":4.2,"crop_stage":"Maturity","moisture":12,"temperature":36,"rainfall":0,"water_need":58,"lat":16.50,"lon":75.29,"last_irrigated":"2026-11-04","electricity":"Unavailable"},
    {"id":"SC1004","farmer":"Anita Desai","village":"Lokapur","area":1.8,"crop_stage":"Grand Growth","moisture":42,"temperature":29,"rainfall":12,"water_need":0,"lat":16.18,"lon":75.35,"last_irrigated":"2026-11-08","electricity":"Available"},
    {"id":"SC1005","farmer":"Prakash Jadhav","village":"Rabkavi","area":5.0,"crop_stage":"Tillering","moisture":22,"temperature":33,"rainfall":1,"water_need":30,"lat":16.48,"lon":75.10,"last_irrigated":"2026-11-05","electricity":"Available"},
    {"id":"SC1006","farmer":"Meena Hegde","village":"Terdal","area":2.7,"crop_stage":"Maturity","moisture":27,"temperature":31,"rainfall":0,"water_need":22,"lat":16.42,"lon":75.42,"last_irrigated":"2026-11-07","electricity":"Unavailable"},
    {"id":"SC1007","farmer":"Suresh Gowda","village":"Bilgi","area":3.1,"crop_stage":"Grand Growth","moisture":15,"temperature":35,"rainfall":0,"water_need":49,"lat":16.35,"lon":75.55,"last_irrigated":"2026-11-05","electricity":"Available"},
    {"id":"SC1008","farmer":"Lata More","village":"Kerur","area":2.4,"crop_stage":"Tillering","moisture":35,"temperature":28,"rainfall":8,"water_need":8,"lat":16.08,"lon":75.22,"last_irrigated":"2026-11-08","electricity":"Available"},
]

IRRIGATION_LOG = []
UNDO_STACK = []
REQUEST_QUEUE = deque()
NEXT_LOG_ID = 1

# -------------------- Data structures --------------------
class Stack:
    """LIFO stack: most recent action is undone first."""
    def __init__(self): self.items = []
    def push(self, item): self.items.append(item)
    def pop(self): return self.items.pop() if self.items else None
    def peek(self): return self.items[-1] if self.items else None
    def __len__(self): return len(self.items)

class SinglyNode:
    def __init__(self, data): self.data, self.next = data, None

class SinglyLinkedList:
    def __init__(self): self.head = None
    def append(self, data):
        node = SinglyNode(data)
        if not self.head: self.head = node; return
        cur = self.head
        while cur.next: cur = cur.next
        cur.next = node
    def values(self):
        out, cur = [], self.head
        while cur: out.append(cur.data); cur = cur.next
        return out

class DoublyNode:
    def __init__(self, data): self.data, self.prev, self.next = data, None, None

class DoublyLinkedList:
    def __init__(self): self.head = self.tail = None
    def append(self, data):
        node = DoublyNode(data)
        if not self.head: self.head = self.tail = node; return
        node.prev = self.tail; self.tail.next = node; self.tail = node
    def forward(self):
        out, cur = [], self.head
        while cur: out.append(cur.data); cur = cur.next
        return out
    def backward(self):
        out, cur = [], self.tail
        while cur: out.append(cur.data); cur = cur.prev
        return out

class CircularLinkedList:
    def __init__(self): self.head = None
    def append(self, data):
        node = SinglyNode(data)
        if not self.head:
            self.head = node; node.next = node; return
        cur = self.head
        while cur.next != self.head: cur = cur.next
        cur.next = node; node.next = self.head
    def cycle(self, count=8):
        out, cur = [], self.head
        if not cur: return out
        for _ in range(min(count, 20)):
            out.append(cur.data); cur = cur.next
        return out

class BSTNode:
    def __init__(self, key, farm_id): self.key, self.farm_id, self.left, self.right = key, farm_id, None, None

class MoistureBST:
    def __init__(self): self.root = None
    def insert(self, key, farm_id):
        def add(node):
            if not node: return BSTNode(key, farm_id)
            if key < node.key: node.left = add(node.left)
            else: node.right = add(node.right)
            return node
        self.root = add(self.root)
    def inorder(self):
        out = []
        def walk(n):
            if n:
                walk(n.left); out.append({"moisture":n.key,"farm_id":n.farm_id}); walk(n.right)
        walk(self.root); return out

class KDNode:
    def __init__(self, point, axis, left=None, right=None):
        self.point, self.axis, self.left, self.right = point, axis, left, right

class KDTree:
    """2D k-d tree for nearest farm coordinate lookup."""
    def __init__(self, points): self.root = self._build(points, 0)
    def _build(self, pts, depth):
        if not pts: return None
        axis = depth % 2; pts = sorted(pts, key=lambda p:p[axis]); mid = len(pts)//2
        return KDNode(pts[mid], axis, self._build(pts[:mid],depth+1), self._build(pts[mid+1:],depth+1))
    def nearest(self, target):
        best = [None, float("inf")]
        def visit(node):
            if not node: return
            p = node.point; d = (p[0]-target[0])**2 + (p[1]-target[1])**2
            if d < best[1]: best[:] = [p,d]
            diff = target[node.axis] - p[node.axis]
            first, second = (node.left,node.right) if diff < 0 else (node.right,node.left)
            visit(first)
            if diff*diff < best[1]: visit(second)
        visit(self.root)
        return best[0], best[1]**0.5

def binary_search(sorted_farms, target):
    """Iterative binary search on sorted plot IDs."""
    low, high = 0, len(sorted_farms)-1
    while low <= high:
        mid = (low+high)//2
        if sorted_farms[mid]["id"] == target: return sorted_farms[mid], mid+1
        if sorted_farms[mid]["id"] < target: low = mid+1
        else: high = mid-1
    return None, 0

def merge_sort(items, key, reverse=False):
    if len(items) <= 1: return items[:]
    mid = len(items)//2
    left, right = merge_sort(items[:mid],key,reverse), merge_sort(items[mid:],key,reverse)
    result = []; i = j = 0
    while i < len(left) and j < len(right):
        a, b = left[i][key], right[j][key]
        take_left = a >= b if reverse else a <= b
        if take_left: result.append(left[i]); i += 1
        else: result.append(right[j]); j += 1
    return result + left[i:] + right[j:]

def urgency(farm):
    if farm["moisture"] < 15: return "Critical"
    if farm["moisture"] < 25: return "High"
    if farm["moisture"] < 35: return "Moderate"
    return "Low"

def advisory(farm):
    level = urgency(farm)
    if farm["rainfall"] >= 10:
        return {"status":"Delay irrigation","duration":0,"reason":"Recent rainfall is sufficient; recheck soil moisture tomorrow.","level":"Low"}
    if farm["moisture"] >= 35:
        return {"status":"No irrigation needed","duration":0,"reason":"Soil moisture is currently adequate.","level":level}
    if farm["electricity"] == "Unavailable":
        return {"status":"Schedule when power is available","duration":0,"reason":"Moisture is low, but electricity is currently unavailable.","level":level}
    duration = round(max(0, (35-farm["moisture"])*0.12 + farm["area"]*0.25), 1)
    return {"status":"Irrigation recommended","duration":duration,"reason":f"Soil moisture is below the prototype threshold of 35%. Crop stage: {farm['crop_stage']}.","level":level}

def all_structures():
    sll, dll, cll, bst = SinglyLinkedList(), DoublyLinkedList(), CircularLinkedList(), MoistureBST()
    for f in FARMS:
        sll.append(f["id"]); dll.append(f["id"]); cll.append(f["id"]); bst.insert(f["moisture"], f["id"])
    return sll, dll, cll, bst

@app.route("/")
def dashboard():
    recs = [(f, advisory(f)) for f in FARMS]
    critical = sum(1 for f,a in recs if a["level"] in ("Critical","High") and a["duration"] > 0)
    total_water = sum(a["duration"] * f["area"] for f,a in recs)
    return render_template("index.html", farms=FARMS, recs=recs, critical=critical,
        avg=round(sum(f["moisture"] for f in FARMS)/len(FARMS),1),
        total_water=round(total_water,1), queue_count=len(REQUEST_QUEUE))

@app.route("/farms", methods=["GET","POST"])
def farms():
    if request.method == "POST":
        fid = request.form.get("id","").strip().upper()
        if not fid or any(f["id"] == fid for f in FARMS):
            flash("Enter a unique plot ID.", "error")
        else:
            try:
                farm = {"id":fid,"farmer":request.form["farmer"].strip(),"village":request.form["village"].strip(),
                    "area":float(request.form["area"]),"crop_stage":request.form["crop_stage"],
                    "moisture":float(request.form["moisture"]),"temperature":float(request.form["temperature"]),
                    "rainfall":float(request.form["rainfall"]),"water_need":0,"lat":float(request.form.get("lat") or 16.3),
                    "lon":float(request.form.get("lon") or 75.3),"last_irrigated":"Not recorded","electricity":request.form["electricity"]}
                if not farm["farmer"] or not farm["village"] or farm["area"] <= 0 or not 0 <= farm["moisture"] <= 100:
                    raise ValueError()
                FARMS.append(farm); UNDO_STACK.append({"action":"add","farm":farm.copy()})
                flash(f"Plot {fid} added successfully.", "success")
            except (ValueError, KeyError):
                flash("Check the form: area must be positive and moisture must be between 0 and 100.", "error")
        return redirect(url_for("farms"))
    return render_template("farms.html", farms=FARMS)

@app.route("/farm/<fid>/delete", methods=["POST"])
def delete_farm(fid):
    farm = next((f for f in FARMS if f["id"] == fid), None)
    if farm:
        FARMS.remove(farm); UNDO_STACK.append({"action":"delete","farm":farm.copy()})
        flash(f"Plot {fid} deleted. You can undo this action.", "success")
    return redirect(request.referrer or url_for("farms"))

@app.route("/undo", methods=["POST"])
def undo():
    action = UNDO_STACK.pop() if UNDO_STACK else None
    if not action: flash("Nothing to undo.", "error")
    elif action["action"] == "add":
        FARMS[:] = [f for f in FARMS if f["id"] != action["farm"]["id"]]
        flash("Last addition undone.", "success")
    else:
        if not any(f["id"] == action["farm"]["id"] for f in FARMS): FARMS.append(action["farm"])
        flash("Last deletion undone.", "success")
    return redirect(request.referrer or url_for("farms"))

@app.route("/search", methods=["GET","POST"])
def search():
    result, comparisons = None, 0
    query = ""
    if request.method == "POST":
        query = request.form.get("plot_id","").strip().upper()
        result, comparisons = binary_search(sorted(FARMS,key=lambda x:x["id"]), query)
    return render_template("search.html", result=result, comparisons=comparisons, query=query)

@app.route("/advisories")
def advisories():
    rows = [(f, advisory(f)) for f in merge_sort(FARMS,"moisture")]
    return render_template("advisories.html", rows=rows)

@app.route("/schedule", methods=["GET","POST"])
def schedule():
    global NEXT_LOG_ID
    if request.method == "POST":
        fid = request.form.get("farm_id")
        farm = next((f for f in FARMS if f["id"] == fid), None)
        if farm:
            a = advisory(farm)
            if a["duration"] > 0:
                REQUEST_QUEUE.append({"farm_id":fid,"farmer":farm["farmer"],"duration":a["duration"],"level":a["level"]})
                flash(f"{fid} added to the irrigation queue.", "success")
            else: flash("This plot has no immediate irrigation task to queue.", "error")
        return redirect(url_for("schedule"))
    return render_template("schedule.html", queue=list(REQUEST_QUEUE), farms=FARMS)

@app.route("/schedule/process", methods=["POST"])
def process_queue():
    global NEXT_LOG_ID
    task = REQUEST_QUEUE.popleft() if REQUEST_QUEUE else None
    if task:
        log = {"log_id":NEXT_LOG_ID,"farm_id":task["farm_id"],"farmer":task["farmer"],
               "duration":task["duration"],"date":datetime.now().strftime("%d %b %Y, %I:%M %p")}
        NEXT_LOG_ID += 1; IRRIGATION_LOG.append(log)
        flash(f"Processed irrigation request for {task['farm_id']} (FIFO).", "success")
    else: flash("The queue is empty.", "error")
    return redirect(url_for("schedule"))

@app.route("/history")
def history():
    sll, dll, cll, bst = all_structures()
    return render_template("history.html", logs=IRRIGATION_LOG, singly=sll.values(),
        doubly_forward=dll.forward(), doubly_backward=dll.backward(), circular=cll.cycle(len(FARMS)+3))

@app.route("/structures")
def structures():
    sll, dll, cll, bst = all_structures()
    sorted_moisture = bst.inorder()
    urgency_heap = []
    for f in FARMS:
        a = advisory(f)
        if a["duration"] > 0:
            rank = {"Critical":0,"High":1,"Moderate":2,"Low":3}[a["level"]]
            heapq.heappush(urgency_heap,(rank, f["moisture"], f["id"]))
    priority = [{"farm_id":heapq.heappop(urgency_heap)[2]} for _ in range(len(urgency_heap))]
    nearest = None
    if FARMS:
        tree = KDTree([(f["lat"],f["lon"],f["id"]) for f in FARMS])
        p, dist = tree.nearest((16.30,75.25))
        nearest = {"farm_id":p[2],"distance":round(dist,4)}
    return render_template("structures.html", stack=UNDO_STACK, queue=list(REQUEST_QUEUE),
        singly=sll.values(), doubly=dll.forward(), circular=cll.cycle(len(FARMS)+2),
        bst=sorted_moisture, priority=priority, nearest=nearest,
        sorted_ids=[f["id"] for f in merge_sort(FARMS,"id")])

@app.route("/api/farms")
def api_farms():
    return jsonify([{"id":f["id"],"farmer":f["farmer"],"moisture":f["moisture"],"urgency":urgency(f)} for f in FARMS])

if __name__ == "__main__":
    app.run(debug=True)
