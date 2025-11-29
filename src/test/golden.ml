open Core

let exists f = match Sys_unix.file_exists f with
  | `No | `Unknown -> false
  | `Yes -> true

let rec find_project_root dir =
  let dune_file = Filename.concat dir "dune-project" in
  if exists dune_file then dir else
    let parent = Filename.dirname dir in
    if Filename.(parent = dir)
    then failwith "Could not find dune-project file"
    else find_project_root parent

let project_root =
  find_project_root @@
  Filename_unix.realpath @@
  Filename.current_dir_name

let test_root = Filename.concat project_root "test"

let should_update = match Sys.getenv "UPDATE_EXPECT" with
  | Some ("1" | "true" | "yes") -> true
  | _ -> false

let write path data =
  assert (Filename.is_relative path);
  let path = Filename.concat test_root path in
  let dir = Filename.dirname path in
  if not (exists dir) then Core_unix.mkdir dir ~perm:0o755;
  Out_channel.write_all path ~data

let compare_or_update ?(chop_end = true) ~fail ~expected_file ~actual () =
  if not (exists expected_file) then
    write expected_file (actual ^ "\n")
  else
    let expected = In_channel.read_all expected_file in
    let expected = if not chop_end then expected
      else String.chop_suffix_if_exists expected ~suffix:"\n" in
    if String.(expected <> actual) then
      if should_update then
        write expected_file (actual ^ "\n")
      else
        let diff =
          Odiff.strings_diffs expected actual |>
          Odiff.string_of_diffs in
        fail @@ Format.sprintf
          "Output mismatch in %s:\n%s"
          expected_file diff
