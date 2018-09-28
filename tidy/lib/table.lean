import data.list
import .array

universes u v w z

def table_ref : Type := ℕ
def table_ref.from_nat (r : ℕ) : table_ref := r
def table_ref.to_nat (r : table_ref) : ℕ := r
def table_ref.to_string (r : table_ref) : string := to_string r.to_nat
def table_ref.next (r : table_ref) : table_ref := table_ref.from_nat (r + 1)
def table_ref.null  : table_ref := table_ref.from_nat 0x8FFFFFFF
def table_ref.first : table_ref := table_ref.from_nat 0
instance : has_to_string table_ref := ⟨λ t, t.to_string⟩

class indexed (α : Type u) :=
(index : α → table_ref)
class keyed (α : Type u) (κ : Type v) [decidable_eq κ] :=
(key : α → κ)

structure table (α : Type u) :=
(next_id : table_ref)
(buff_len : ℕ)
(entries : array buff_len (option α))

namespace table

variables {α : Type u} {β : Type v} {κ : Type w} [decidable_eq κ] (t : table α)

-- TODO use push_back and pop_back builtins to avoid array preallocation
-- TODO several recusion-induced-meta can be removed from the file (given proofs)

def DEFAULT_BUFF_LEN := 10

def create (buff_len : ℕ := DEFAULT_BUFF_LEN) : table α :=
  ⟨ table_ref.first, buff_len, mk_array buff_len none ⟩

meta def from_list (l : list α) : table α :=
  let n := l.length in
  let buff : array n (option α) := mk_array n none in
  ⟨ table_ref.from_nat n, n, buff.list_map_copy (λ a, some a) l⟩

meta def from_map_array {dim : ℕ} (x : array dim α) (f : α → β) : table β :=
  let buff : array dim (option β) := mk_array dim none in
  ⟨table_ref.from_nat dim, dim, x.map_copy buff (λ a, some $ f a)⟩

meta def from_array {dim : ℕ} (x : array dim α) : table α :=
  from_map_array x $ λ a, a

def is_full : bool := t.next_id.to_nat = t.buff_len

private def try_fin (r : table_ref) : option (fin t.buff_len) :=
begin
  let r := r.to_nat,
  by_cases h : r < t.buff_len,
  exact fin.mk r h,
  exact none
end

meta def grow : table α :=
  let new_len := t.buff_len * 2 in
  let new_buff : array new_len (option α) := mk_array new_len none in
  {t with buff_len := new_len, entries := array.copy t.entries new_buff}

def at_ref (r : table_ref) : option α :=
  match try_fin t r with
  | none := none
  | some r := t.entries.read r
  end

meta def get (r : table_ref) : tactic α := t.at_ref r

def iget [inhabited α] (r : table_ref) : α :=
  match t.at_ref r with
  | none := default α
  | some a := a
  end

def set (r : table_ref) (a : α) : table α :=
  match try_fin t r with
  | none := t
  | some r := {t with entries := t.entries.write r a}
  end

meta def alloc (a : α) : table α :=
  let t : table α := if t.is_full then t.grow else t in
  let t := t.set t.next_id a in
  { t with next_id := t.next_id.next }

meta def alloc_list : table α → list α → table α
| t [] := t
| t (a :: rest) := alloc_list (t.alloc a) rest

def update [indexed α] (a : α) : table α := t.set (indexed.index a) a

def length : ℕ := t.next_id.to_nat

meta def find_from (p : α → Prop) [decidable_pred p] : table_ref → option α
| ref := match t.at_ref ref with
  | none := none
  | some a := if p a then some a else find_from ref.next
  end
meta def find (p : α → Prop) [decidable_pred p] : option α := t.find_from p table_ref.first
meta def find_key [decidable_eq κ] [keyed α κ] (key : κ) : option α := t.find (λ a, key = @keyed.key _ _ _ _ a)

meta def foldl (f : β → α → β) (b : β) (t : table α) : β :=
  t.entries.foldl b (λ a : option α, λ b : β, match a with
                                              | none := b
                                              | some a := f b a
                                              end)

meta def map (f : α → β) : table β :=
  let new_buff : array t.buff_len (option β) := mk_array t.buff_len none in
  ⟨t.next_id, t.buff_len, t.entries.map_copy new_buff (λ a : option α, match a with
                                                                       | none := none
                                                                       | some a := f a
                                                                       end)⟩

meta def mmap {m : Type v → Type z} [monad m] (f : α → m β) : m (table β) := do
  let new_buff : array t.buff_len (option β) := mk_array t.buff_len none,
  new_buff ← t.entries.mmap_copy new_buff (λ a : option α, match a with
                                                           | none := pure none
                                                           | some a := do v ← f a, pure $ some v
                                                           end),
  return ⟨t.next_id, t.buff_len, new_buff⟩

def is_after_last (r : table_ref) : bool := t.next_id.to_nat <= r.to_nat

meta def to_list : list α := t.foldl (λ l : list α, λ a : α, l.concat a) []

meta instance [has_to_string α] : has_to_string (table α) := ⟨λ t, to_string t.to_list⟩

end table