import csv
from dxr.languages import register_language_table
from dxr.languages import language_schema
import dxr.plugins
import os
import mmap

decl_master = {}
types = {}
typedefs = {}
functions = {}
inheritance = {}
variables = {}
references = {}
warnings = []
macros = {}
calls = {}
overrides = {}
scopes = {}
functionsToDelete = []
typesToDelete = []

def process_decldef(args):
  # Wait for post-processing
  name, defloc, declloc = args['name'], args['defloc'], args['declloc']
  decl_master[(name, declloc)] = defloc
  decl_master[(name, defloc)] = defloc
  return None

def process_type(args):
  args['tid'] = dxr.plugins.next_global_id()
  return language_schema.get_insert_sql('types', args)
#  types[(typeinfo['tqualname'], typeinfo['tloc'])] = typeinfo

def process_typedef(args):
  args['tid'] = dxr.plugins.next_global_id()
  return schema.get_insert_sql('typedefs', args)

def process_function(args):
  args['funcid'] = dxr.plugins.next_global_id()
  if 'overridename' in args:
    overrides[args['funcid']] = (args['overridename'], args['overrideloc'])
  return language_schema.get_insert_sql('functions', args)
#  functions[(funcinfo['fqualname'], funcinfo['floc'])] = funcinfo

def process_impl(args):
#  return language_schema.get_insert_sql('impl', args)
  inheritance[args['tbname'], args['tbloc'], args['tcname'], args['tcloc']] = args
  return None

def process_variable(args):
  args['varid'] = dxr.plugins.next_global_id()
  return language_schema.get_insert_sql('variables', args)
#  variables[varinfo['vname'], varinfo['vloc']] = varinfo

def process_ref(args):
  if 'extent' not in args:
    return None

  args['refid'] = dxr.plugins.next_global_id()
  return schema.get_insert_sql('refs', args)
  # Each reference is pretty much unique, but we might record it several times
  # due to header files.
#  references[info['varname'], info['varloc'], info['refloc']] = info

def process_warning(args):
  return schema.get_insert_sql('warnings', args)

def process_macro(args):
  args['macroid'] = dxr.plugins.next_global_id()
  if 'macrotext' in args:
    args['macrotext'] = args['macrotext'].replace("\\\n", "\n").strip()
  return schema.get_insert_sql('macros', args)

def process_call(args):
  if 'callername' in args:
    calls[args['callername'], args['callerloc'],
          args['calleename'], args['calleeloc']] = args
  else:
    calls[args['calleename'], args['calleeloc']] = args

  return None

def load_indexer_output(fname):
  f = open(fname, "rb")
  try:
    parsed_iter = csv.reader(f)
    for line in parsed_iter:
      # Our first column is the type that we're reading, the others are just
      # an args array to be passed in
      argobj = {}
      for i in range(1, len(line), 2):
        argobj[line[i]] = line[i + 1]
      globals()['process_' + line[0]](argobj)
  except:
    print fname, line
    raise
  finally:
    f.close()

def dump_indexer_output(conn, fname):
  f = open(fname, 'r')

  try:
    parsed_iter = csv.reader(f)
    for line in parsed_iter:
      args = {}
      # Our first column is the type that we're reading, the others are just
      # a key/value pairs array to be passed in
      for i in range(1, len(line), 2):
        args[line[i]] = line[i + 1]

      stmt = globals()['process_' + line[0]](args)

      if stmt is None:
        continue

      if isinstance(stmt, tuple):
        conn.execute(stmt[0], stmt[1])
      else:
        conn.execute(stmt)
  except IndexError, e:
    raise e
  finally:
    f.close()

file_names = []
def collect_files(arg, dirname, fnames):
  for name in fnames:
    if os.path.isdir(name): continue
    if not name.endswith(arg): continue
    file_names.append(os.path.join(dirname, name))

def canonicalize_decl(name, loc):
  return (name, decl_master.get((name, loc), loc))

def recanon_decl(name, loc):
  decl_master[name, loc] = (name, loc)
  return (name, loc)

def fixup_scope(conn):
  global typesToDelete
  global functionsToDelete
  global scopes

  for row in conn.execute("SELECT tqualname, tloc, tid FROM types").fetchall():
    key = canonicalize_decl(row[0], row[1])

#    if key not in types:
#      key = recanon_decl(row[0], row[1])

    if key not in scopes:
      scopes[key] = dxr.plugins.next_global_id()
    else:
      typesToDelete.append(str(row[2]))

  for row in conn.execute("SELECT fqualname, floc, funcid FROM functions").fetchall():
    key = canonicalize_decl(row[0], row[1])
#    if key not in functions:
#      key = recanon_decl(f[0], f[1])
    if key not in scopes:
      scopes[key] = dxr.plugins.next_global_id()
    else:
      functionsToDelete.append(str(row[2]))

  for data, scopeid in scopes.iteritems():
    conn.execute ("INSERT INTO scopes (scopeid, sname, sloc, language) VALUES (?, ?, ?, ?)",
                  (scopeid, data[0], data[1], "native"))

def build_inherits(base, child, direct):
  db = { 'tbase': base, 'tderived': child }
  if direct is not None:
    db['inhtype'] = direct
  return db

def generate_inheritance(conn):
  childMap, parentMap = {}, {}
  types = {}

  for row in conn.execute("SELECT tqualname, tloc, tid from types").fetchall():
    types[(row[0], row[1])] = row[2]

  for infoKey in inheritance:
    info = inheritance[infoKey]
    try:
      base = types[canonicalize_decl(info['tbname'], info['tbloc'])]
      child = types[canonicalize_decl(info['tcname'], info['tcloc'])]
    except KeyError:
      continue

    conn.execute("INSERT OR IGNORE INTO impl(tbase, tderived, inhtype) VALUES (?, ?, ?)",
                 (base, child, info.get('access', '')))

    # Get all known relations
    subs = childMap.setdefault(child, [])
    supers = parentMap.setdefault(base, [])
    # Use this information
    for sub in subs:
      conn.execute("INSERT OR IGNORE INTO impl(tbase, tderived) VALUES (?, ?)",
                   (base, sub))
      parentMap[sub].append(base)
    for sup in supers:
      conn.execute("INSERT OR IGNORE INTO impl(tbase, tderived) VALUES (?, ?)",
                   (sup, child))
      childMap[sup].append(child)

    # Carry through these relations
    newsubs = childMap.setdefault(base, [])
    newsubs.append(child)
    newsubs.extend(subs)
    newsupers = parentMap.setdefault(child, [])
    newsupers.append(base)
    newsupers.extend(supers)


def generate_callgraph(conn):
  functions = {}
  variables = {}
  callgraph = []

  print "Generating callers..."

  for row in conn.execute("SELECT fqualname, floc, funcid FROM functions").fetchall():
    functions[(row[0], row[1])] = row[2]

  for row in conn.execute("SELECT vname, vloc, varid FROM variables").fetchall():
    variables[(row[0], row[1])] = row[2]

  # Generate callers table
  for call in calls.values():
    if 'callername' in call:
      source = canonicalize_decl(call['callername'],call['callerloc'])
      call['callerid'] = functions.get(source)

      if call['callerid'] is None:
        continue
    else:
      call['callerid'] = 0

    target = canonicalize_decl(call['calleename'], call['calleeloc'])
    targetid = functions.get(target)

    if targetid is None:
      targetid = variables.get(target)

    if targetid is not None:
      call['targetid'] = targetid
      callgraph.append(call)

  del variables
  del functions

  for i in range(0, len(functionsToDelete), 20):
    conn.execute ("DELETE FROM functions WHERE funcid IN (%s)" % ','.join(functionsToDelete[i:i + 20]))

  for i in range(0, len(typesToDelete), 20):
    conn.execute ("DELETE FROM types WHERE tid IN (%s)" % ','.join(typesToDelete[i:i + 20]))

  functions = {}
  for row in conn.execute("SELECT fqualname, floc, funcid FROM functions").fetchall():
    functions[(row[0], row[1])] = row[2]

  print "Generating targets..."

  # Generate targets table
  overridemap = {}

  for func, funcid in functions.iteritems():
    override = overrides.get(funcid)

    if override is None:
      continue

    base = canonicalize_decl(override[0], override[1])
    basekey = functions.get(base)

    if basekey is None:
      continue

    overridemap.setdefault(basekey, set()).add(funcid)

  rescan = [x for x in overridemap]
  while len(rescan) > 0:
    base = rescan.pop(0)
    childs = overridemap[base]
    prev = len(childs)
    temp = childs.union(*(overridemap.get(sub, []) for sub in childs))
    childs.update(temp)
    if len(childs) != prev:
      rescan.append(base)

  for base, childs in overridemap.iteritems():
    conn.execute("INSERT INTO targets (targetid, funcid) VALUES (?, ?)",
                 (-base, base));

    for child in childs:
      conn.execute("INSERT INTO targets (targetid, funcid) VALUES (?, ?)",
                   (-base, child));

  for call in callgraph:
    if call['calltype'] == 'virtual':
      targetid = call['targetid']
      call['targetid'] = -targetid
      if targetid not in overridemap:
        overridemap[targetid] = set()
        conn.execute("INSERT INTO targets (targetid, funcid) VALUES (?, ?)",
                     (-targetid, targetid));
    conn.execute("INSERT OR IGNORE INTO callers (callerid, targetid) VALUES (?, ?)",
                  (call['callerid'], call['targetid']))


def post_process(srcdir, objdir):
  return None


def build_database(conn, srcdir, objdir, cache=None):
  count = 0
  os.path.walk(objdir, collect_files, ".csv")

  if file_names == []:
    raise IndexError('No .csv files in %s' % objdir)
  for f in file_names:
    dump_indexer_output(conn, f)
    count = count + 1

    if count % 1000 == 0:
      conn.commit()

  print "Fixing up scopes..."
  fixup_scope(conn)
  print "Generating callgraph..."
  generate_callgraph(conn)
  print "Generating inheritances..."
  generate_inheritance(conn)

  conn.commit()

  return None

def pre_html_process(treecfg, blob):
#  blob["byfile"] = dxr.plugins.break_into_files(blob, {
#    "refs": "refloc",
#    "warnings": "wloc",
#    "decldef": "declloc",
#    "macros": "macroloc"
#  })
  return

def sqlify(blob):
#  return schema.get_data_sql(blob)
  return

def can_use(treecfg):
  # We need to have clang and llvm-config in the path
  return dxr.plugins.in_path('clang') and dxr.plugins.in_path('llvm-config')

schema = dxr.plugins.Schema({
  # Typedef information in the tables
  "typedefs": [
    ("tid", "INTEGER", False),           # The typedef's tid (also in types)
    ("ttypedef", "VARCHAR(256)", False), # The long name of the type
    ("_key", "tid"),
    ("_index", "ttypedef")
  ],
  # References to functions, types, variables, etc.
  "refs": [
    ("refid", "INTEGER", False),      # ID of the identifier being referenced
    ("refloc", "_location", False),   # Location of the reference
    ("extent", "VARCHAR(30)", True), # Extent (start:end) of the reference
    ("_key", "refid", "refloc"),
    ("_index", "refloc", "extent")
  ],
  # Warnings found while compiling
  "warnings": {
    "wloc": ("_location", False),   # Location of the warning
    "wmsg": ("VARCHAR(256)", False) # Text of the warning
  },
  # Declaration/definition mapping
  "decldef": {
    "defid": ("INTEGER", False),    # ID of the definition instance
    "declloc": ("_location", False) # Location of the declaration
  },
  # Macros: this is a table of all of the macros we come across in the code.
  "macros": [
     ("macroid", "INTEGER", False),        # The macro id, for references
     ("macroloc", "_location", False),     # The macro definition
     ("macroname", "VARCHAR(256)", False), # The name of the macro
     ("macroargs", "VARCHAR(256)", True),  # The args of the macro (if any)
     ("macrotext", "TEXT", True),          # The macro contents
     ("_key", "macroid", "macroloc"),
     ("_index", "macroname", "macroloc")
  ],
  # The following two tables are combined to form the callgraph implementation.
  # In essence, the callgraph can be viewed as a kind of hypergraph, where the
  # edges go from functions to sets of functions and variables. For use in the
  # database, we are making some big assumptions: the targetid is going to be
  # either a function or variable (the direct thing we called); if the function
  # is virtual or the target is a variable, we use the targets table to identify
  # what the possible implementations could be.
  "callers": [
    ("callerid", "INTEGER", False), # The function in which the call occurs
    ("targetid", "INTEGER", False), # The target of the call
    ("_key", "callerid", "targetid")
  ],
  "targets": [
    ("targetid", "INTEGER", False), # The target of the call
    ("funcid", "INTEGER", False),   # One of the functions in the target set
    ("_key", "targetid", "funcid")
  ]
})

get_schema = dxr.plugins.make_get_schema_func(schema)

import dxr
from dxr.tokenizers import CppTokenizer
class CxxHtmlifier:
  def __init__(self, blob, srcpath, treecfg, conn):
    self.source = dxr.readFile(srcpath)
    self.srcpath = srcpath.replace(treecfg.sourcedir + '/', '')
    self.blob_file = None #blob["byfile"].get(self.srcpath, None)
    self.conn = conn

  def collectSidebar(self):
    def line(linestr):
      return linestr.split(':')[1]
    def make_tuple(df, name, loc, scope="scopeid", decl=False):
      if decl:
        img = 'images/icons/page_white_code.png'
      else:
        loc = df[loc]
        img = 'images/icons/page_white_wrench.png'
      if scope in df and df[scope] > 0:
        return (df[name], loc.split(':')[1], df[name], img,
          dxr.languages.get_row_for_id("scopes", df[scope])["sname"])
      return (df[name], loc.split(':')[1], df[name], img)
    for row in self.conn.execute("SELECT tqualname, tloc, scopeid FROM types WHERE tloc GLOB '%s*'" % (self.srcpath,)).fetchall():
      yield make_tuple(row, "tqualname", "tloc", "scopeid")
    for row in self.conn.execute("SELECT fqualname, floc, scopeid FROM functions WHERE floc GLOB '%s*'" % (self.srcpath,)).fetchall():
      yield make_tuple(row, "fqualname", "floc", "scopeid")
    for row in self.conn.execute("SELECT vname, vloc, scopeid FROM variables WHERE vloc GLOB '%s*'" % (self.srcpath,)).fetchall():
#      if "scopeid" in row and dxr.languages.get_row_for_id("functions", df["scopeid"]) is not None:
#        continue
      yield make_tuple(row, "vname", "vloc", "scopeid")
    tblmap = { "functions": "fqualname", "types": "tqualname" }
#    for df in self.blob_file["decldef"]:
#      table = df["table"]
#      if table in tblmap:
#        yield make_tuple(dxr.languages.get_row_for_id(table, df["defid"]), tblmap[table],
#          df["declloc"], "scopeid", True)
    for row in self.conn.execute("SELECT macroname, macroloc FROM macros WHERE macroloc GLOB '%s*'" % (self.srcpath,)).fetchall():
      yield make_tuple(row, "macroname", "macroloc")

  def getSyntaxRegions(self):
    self.tokenizer = CppTokenizer(self.source)
    for token in self.tokenizer.getTokens():
      if token.token_type == self.tokenizer.KEYWORD:
        yield (token.start, token.end, 'k')
      elif token.token_type == self.tokenizer.STRING:
        yield (token.start, token.end, 'str')
      elif token.token_type == self.tokenizer.COMMENT:
        yield (token.start, token.end, 'c')
      elif token.token_type == self.tokenizer.PREPROCESSOR:
        yield (token.start, token.end, 'p')

  def getLinkRegions(self):
    def make_link(obj, clazz, rid):
      start, end = obj['extent'].split(':')
      start, end = int(start), int(end)
      kwargs = {}
      kwargs['rid'] = rid
      kwargs['class'] = clazz
      return (start, end, kwargs)
#    tblmap = {
#      "variables": ("var", "varid"),
#      "functions": ("func", "funcid"),
#      "types": ("t", "tid"),
#      "refs": ("ref", "refid"),
#    }
#    for tablename in tblmap:
#      tbl = self.blob_file[tablename]
#      kind, rid = tblmap[tablename]
#      for df in tbl:
#        if 'extent' in df:
#          yield make_link(df, kind, df[rid])
#    for decl in self.blob_file["decldef"]:
#      if 'extent' not in decl: continue
#      yield make_link(decl, tblmap[decl["table"]][0], decl["defid"])

    for row in self.conn.execute("SELECT refid, refloc, extent FROM refs WHERE refloc GLOB '%s*'" % (self.srcpath,)).fetchall():
      yield make_link(row, "ref", row['refid'])

    for row in self.conn.execute("SELECT macroid, macroname, macroloc FROM macros WHERE macroloc GLOB '%s*'" % (self.srcpath,)).fetchall():
      line, col = row['macroloc'].split(':')[1:]
      line, col = int(line), int(col)
      yield ((line, col), (line, col + len(row['macroname'])),
        {'class': 'm', 'rid': row['macroid']})

  def getLineAnnotations(self):
    for row in self.conn.execute("SELECT wmsg, wloc FROM warnings WHERE wloc GLOB '%s*'" % (self.srcpath,)).fetchall():
      line = int(row[1].split(":")[1])
      yield (line, {"class": "lnw", "title": row[0]})

def get_sidebar_links(blob, srcpath, treecfg, conn=None):
  if srcpath not in htmlifier_store:
    htmlifier_store[srcpath] = CxxHtmlifier(blob, srcpath, treecfg, conn)
  return htmlifier_store[srcpath].collectSidebar()
def get_link_regions(blob, srcpath, treecfg, conn=None):
  if srcpath not in htmlifier_store:
    htmlifier_store[srcpath] = CxxHtmlifier(blob, srcpath, treecfg, conn)
  return htmlifier_store[srcpath].getLinkRegions()
def get_line_annotations(blob, srcpath, treecfg, conn=None):
  if srcpath not in htmlifier_store:
    htmlifier_store[srcpath] = CxxHtmlifier(blob, srcpath, treecfg, conn)
  return htmlifier_store[srcpath].getLineAnnotations()
def get_syntax_regions(blob, srcpath, treecfg, conn=None):
  if srcpath not in htmlifier_store:
    htmlifier_store[srcpath] = CxxHtmlifier(blob, srcpath, treecfg, conn)
  return htmlifier_store[srcpath].getSyntaxRegions()
htmlifier_store = {}

htmlifier = {}
for f in ('.c', '.cc', '.cpp', '.h', '.hpp'):
  htmlifier[f] = {'get_sidebar_links': get_sidebar_links,
      'get_link_regions': get_link_regions,
      'get_line_annotations': get_line_annotations,
      'get_syntax_regions': get_syntax_regions}

def get_htmlifiers():
  return htmlifier

__all__ = dxr.plugins.required_exports()
