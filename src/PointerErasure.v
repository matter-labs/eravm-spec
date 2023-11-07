Require Common Pointer.
Import Common Pointer.

(** # Pointer Erasure (since v1.4.1)

Recall that [%fat_ptr] contain four fields:

```
Record fat_ptr_layout := mk_fat_ptr_layout {
                              length: u32;
                              start: u32;
                              page: u32;
                              offset: u32;
                            }.
```

In kernel mode, these fields are observable by all instructions, even by those that work with integers.

In user mode, [%fat_ptr] are opaque: if an instruction expects an integer (with
a cleared [%is_ptr] tag), and it is provided a pointer instead (with a set
[%is_ptr] tag), the pointer value is downcast to the integer before the
instruction is able to observe it.

The downcasting zeroes the fields [%page] and [%start].
 *)
Section PointerErasure.
  Context (is_kernel_mode: bool).

  Definition span_erase (s:span) : span :=
    if is_kernel_mode then s else
      match s with
      | mk_span start len => mk_span # 0 len
      end
  .

  Definition free_ptr_erase (fp: free_ptr) : free_ptr :=
    if is_kernel_mode then fp else
      match fp with
      | mk_ptr s ofs => mk_ptr (span_erase s) ofs
      end
  .

  Definition fat_ptr_erase (fp:fat_ptr) : fat_ptr:=
    if is_kernel_mode then fp else
      match fp with
      | mk_fat_ptr page ptr => mk_fat_ptr 0%nat (free_ptr_erase ptr)
      end
  .

  Definition fat_ptr_nullable_erase (fp:fat_ptr_nullable) : fat_ptr_nullable :=
    if is_kernel_mode then fp else
      match fp with
      | NullPtr => NullPtr
      | NotNullPtr fp => NotNullPtr (fat_ptr_erase fp)
      end.

End PointerErasure.
