open Prims
type ident =
  {
  idText: Prims.string ;
  text_hash: FStar_Util.hash_val ;
  idRange: FStar_Range.range }[@@deriving yojson,show]
let (__proj__Mkident__item__idText : ident -> Prims.string) =
  fun projectee  ->
    match projectee with | { idText; text_hash; idRange;_} -> idText
  
let (__proj__Mkident__item__text_hash : ident -> FStar_Util.hash_val) =
  fun projectee  ->
    match projectee with | { idText; text_hash; idRange;_} -> text_hash
  
let (__proj__Mkident__item__idRange : ident -> FStar_Range.range) =
  fun projectee  ->
    match projectee with | { idText; text_hash; idRange;_} -> idRange
  
type path = Prims.string Prims.list[@@deriving yojson,show]
type ipath = ident Prims.list[@@deriving yojson,show]
type lident =
  {
  ns: ipath ;
  ident: ident ;
  nsstr: Prims.string ;
  str_hash: FStar_Util.hash_val ;
  str: Prims.string }[@@deriving yojson,show]
let (__proj__Mklident__item__ns : lident -> ipath) =
  fun projectee  ->
    match projectee with | { ns; ident; nsstr; str_hash; str;_} -> ns
  
let (__proj__Mklident__item__ident : lident -> ident) =
  fun projectee  ->
    match projectee with | { ns; ident; nsstr; str_hash; str;_} -> ident
  
let (__proj__Mklident__item__nsstr : lident -> Prims.string) =
  fun projectee  ->
    match projectee with | { ns; ident; nsstr; str_hash; str;_} -> nsstr
  
let (__proj__Mklident__item__str_hash : lident -> FStar_Util.hash_val) =
  fun projectee  ->
    match projectee with | { ns; ident; nsstr; str_hash; str;_} -> str_hash
  
let (__proj__Mklident__item__str : lident -> Prims.string) =
  fun projectee  ->
    match projectee with | { ns; ident; nsstr; str_hash; str;_} -> str
  
type lid = lident[@@deriving yojson,show]
let (mk_ident : (Prims.string * FStar_Range.range) -> ident) =
  fun uu____166  ->
    match uu____166 with
    | (text,range) ->
        let uu____176 = FStar_Util.phys_hash text  in
        { idText = text; text_hash = uu____176; idRange = range }
  
let (set_id_range : FStar_Range.range -> ident -> ident) =
  fun r  ->
    fun i  ->
      let uu___29_189 = i  in
      {
        idText = (uu___29_189.idText);
        text_hash = (uu___29_189.text_hash);
        idRange = r
      }
  
let (reserved_prefix : Prims.string) = "uu___" 
let (_gen : ((unit -> Prims.int) * (unit -> unit))) =
  let x = FStar_Util.mk_ref Prims.int_zero  in
  let next_id uu____217 =
    let v1 = FStar_ST.read x  in FStar_ST.write x (v1 + Prims.int_one); v1
     in
  let reset uu____269 = FStar_ST.write x Prims.int_zero  in (next_id, reset) 
let (next_id : unit -> Prims.int) =
  fun uu____305  -> FStar_Pervasives_Native.fst _gen () 
let (reset_gensym : unit -> unit) =
  fun uu____318  -> FStar_Pervasives_Native.snd _gen () 
let (gen' : Prims.string -> FStar_Range.range -> ident) =
  fun s  ->
    fun r  ->
      let i = next_id ()  in
      let uu____341 =
        let uu____347 =
          let uu____349 = FStar_Util.string_of_int i  in
          Prims.op_Hat s uu____349  in
        (uu____347, r)  in
      mk_ident uu____341
  
let (gen : FStar_Range.range -> ident) = fun r  -> gen' reserved_prefix r 
let (ident_of_lid : lident -> ident) = fun l  -> l.ident 
let (range_of_id : ident -> FStar_Range.range) = fun id1  -> id1.idRange 
let (id_of_text : Prims.string -> ident) =
  fun str  -> mk_ident (str, FStar_Range.dummyRange) 
let (text_of_id : ident -> Prims.string) = fun id1  -> id1.idText 
let (text_of_path : path -> Prims.string) =
  fun path  -> FStar_Util.concat_l "." path 
let (path_of_text : Prims.string -> path) =
  fun text  -> FStar_String.split [46] text 
let (path_of_ns : ipath -> path) = fun ns  -> FStar_List.map text_of_id ns 
let (path_of_lid : lident -> path) =
  fun lid  ->
    FStar_List.map text_of_id (FStar_List.append lid.ns [lid.ident])
  
let (ns_of_lid : lident -> ipath) = fun lid  -> lid.ns 
let (ids_of_lid : lident -> ipath) =
  fun lid  -> FStar_List.append lid.ns [lid.ident] 
let (lid_of_ns_and_id : ipath -> ident -> lident) =
  fun ns  ->
    fun id1  ->
      let nsstr =
        let uu____444 = FStar_List.map text_of_id ns  in
        FStar_All.pipe_right uu____444 text_of_path  in
      let s =
        if nsstr = ""
        then id1.idText
        else Prims.op_Hat nsstr (Prims.op_Hat "." id1.idText)  in
      let uu____456 = FStar_Util.phys_hash s  in
      { ns; ident = id1; nsstr; str_hash = uu____456; str = s }
  
let (lid_of_ids : ipath -> lident) =
  fun ids  ->
    let uu____464 = FStar_Util.prefix ids  in
    match uu____464 with | (ns,id1) -> lid_of_ns_and_id ns id1
  
let (lid_of_str : Prims.string -> lident) =
  fun str  ->
    let uu____485 = FStar_List.map id_of_text (FStar_Util.split str ".")  in
    lid_of_ids uu____485
  
let (lid_of_path : path -> FStar_Range.range -> lident) =
  fun path  ->
    fun pos  ->
      let ids = FStar_List.map (fun s  -> mk_ident (s, pos)) path  in
      lid_of_ids ids
  
let (text_of_lid : lident -> Prims.string) = fun lid  -> lid.str 
let (lid_equals : lident -> lident -> Prims.bool) =
  fun l1  -> fun l2  -> (l1.str_hash = l2.str_hash) && (l1.str = l2.str) 
let (ident_equals : ident -> ident -> Prims.bool) =
  fun id1  ->
    fun id2  -> (id1.text_hash = id2.text_hash) && (id1.idText = id2.idText)
  
let (range_of_lid : lident -> FStar_Range.range) =
  fun lid  -> range_of_id lid.ident 
let (set_lid_range : lident -> FStar_Range.range -> lident) =
  fun l  ->
    fun r  ->
      let uu___76_557 = l  in
      {
        ns = (uu___76_557.ns);
        ident =
          (let uu___78_559 = l.ident  in
           {
             idText = (uu___78_559.idText);
             text_hash = (uu___78_559.text_hash);
             idRange = r
           });
        nsstr = (uu___76_557.nsstr);
        str_hash = (uu___76_557.str_hash);
        str = (uu___76_557.str)
      }
  
let (lid_add_suffix : lident -> Prims.string -> lident) =
  fun l  ->
    fun s  ->
      let path = path_of_lid l  in
      let uu____574 = range_of_lid l  in
      lid_of_path (FStar_List.append path [s]) uu____574
  
let (ml_path_of_lid : lident -> Prims.string) =
  fun lid  ->
    let uu____585 =
      let uu____589 = path_of_ns lid.ns  in
      let uu____593 = let uu____597 = text_of_id lid.ident  in [uu____597]
         in
      FStar_List.append uu____589 uu____593  in
    FStar_All.pipe_left (FStar_String.concat "_") uu____585
  
let (string_of_lid : lident -> Prims.string) = fun lid  -> lid.str 
let (qual_id : lident -> ident -> lident) =
  fun lid  ->
    fun id1  ->
      let uu____625 = lid_of_ids (FStar_List.append lid.ns [lid.ident; id1])
         in
      let uu____626 = range_of_id id1  in set_lid_range uu____625 uu____626
  
let (nsstr : lident -> Prims.string) = fun l  -> l.nsstr 