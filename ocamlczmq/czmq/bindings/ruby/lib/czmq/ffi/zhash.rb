################################################################################
#  THIS FILE IS 100% GENERATED BY ZPROJECT; DO NOT EDIT EXCEPT EXPERIMENTALLY  #
#  Please refer to the README for information about making permanent changes.  #
################################################################################

module CZMQ
  module FFI

    # generic type-free hash container (simple)
    # @note This class is 100% generated using zproject.
    class Zhash
      # Raised when one tries to use an instance of {Zhash} after
      # the internal pointer to the native object has been nullified.
      class DestroyedError < RuntimeError; end

      # Boilerplate for self pointer, initializer, and finalizer
      class << self
        alias :__new :new
      end
      # Attaches the pointer _ptr_ to this instance and defines a finalizer for
      # it if necessary.
      # @param ptr [::FFI::Pointer]
      # @param finalize [Boolean]
      def initialize(ptr, finalize = true)
        @ptr = ptr
        if @ptr.null?
          @ptr = nil # Remove null pointers so we don't have to test for them.
        elsif finalize
          @finalizer = self.class.create_finalizer_for @ptr
          ObjectSpace.define_finalizer self, @finalizer
        end
      end
      # @param ptr [::FFI::Pointer]
      # @return [Proc]
      def self.create_finalizer_for(ptr)
        Proc.new do
          ptr_ptr = ::FFI::MemoryPointer.new :pointer
          ptr_ptr.write_pointer ptr
          ::CZMQ::FFI.zhash_destroy ptr_ptr
        end
      end
      # @return [Boolean]
      def null?
        !@ptr or @ptr.null?
      end
      # Return internal pointer
      # @return [::FFI::Pointer]
      def __ptr
        raise DestroyedError unless @ptr
        @ptr
      end
      # So external Libraries can just pass the Object to a FFI function which expects a :pointer
      alias_method :to_ptr, :__ptr
      # Nullify internal pointer and return pointer pointer.
      # @note This detaches the current instance from the native object
      #   and thus makes it unusable.
      # @return [::FFI::MemoryPointer] the pointer pointing to a pointer
      #   pointing to the native object
      def __ptr_give_ref
        raise DestroyedError unless @ptr
        ptr_ptr = ::FFI::MemoryPointer.new :pointer
        ptr_ptr.write_pointer @ptr
        __undef_finalizer if @finalizer
        @ptr = nil
        ptr_ptr
      end
      # Undefines the finalizer for this object.
      # @note Only use this if you need to and can guarantee that the native
      #   object will be freed by other means.
      # @return [void]
      def __undef_finalizer
        ObjectSpace.undefine_finalizer self
        @finalizer = nil
      end

      # Create a new callback of the following type:
      # Callback function for zhash_freefn method
      #     typedef void (zhash_free_fn) (
      #         void *data);              
      #
      # @note WARNING: If your Ruby code doesn't retain a reference to the
      #   FFI::Function object after passing it to a C function call,
      #   it may be garbage collected while C still holds the pointer,
      #   potentially resulting in a segmentation fault.
      def self.free_fn
        ::FFI::Function.new :void, [:pointer], blocking: true do |data|
          result = yield data
          result
        end
      end

      # Create a new callback of the following type:
      # DEPRECATED as clumsy -- use zhash_first/_next instead
      #     typedef int (zhash_foreach_fn) (                 
      #         const char *key, void *item, void *argument);
      #
      # @note WARNING: If your Ruby code doesn't retain a reference to the
      #   FFI::Function object after passing it to a C function call,
      #   it may be garbage collected while C still holds the pointer,
      #   potentially resulting in a segmentation fault.
      def self.foreach_fn
        ::FFI::Function.new :int, [:string, :pointer, :pointer], blocking: true do |key, item, argument|
          result = yield key, item, argument
          result = Integer(result)
          result
        end
      end

      # Create a new, empty hash container
      # @return [CZMQ::Zhash]
      def self.new()
        ptr = ::CZMQ::FFI.zhash_new()
        __new ptr
      end

      # Unpack binary frame into a new hash table. Packed data must follow format
      # defined by zhash_pack. Hash table is set to autofree. An empty frame     
      # unpacks to an empty hash table.                                          
      # @param frame [Zframe, #__ptr]
      # @return [CZMQ::Zhash]
      def self.unpack(frame)
        frame = frame.__ptr if frame
        ptr = ::CZMQ::FFI.zhash_unpack(frame)
        __new ptr
      end

      # Destroy a hash container and all items in it
      #
      # @return [void]
      def destroy()
        return unless @ptr
        self_p = __ptr_give_ref
        result = ::CZMQ::FFI.zhash_destroy(self_p)
        result
      end

      # Insert item into hash table with specified key and item.               
      # If key is already present returns -1 and leaves existing item unchanged
      # Returns 0 on success.                                                  
      #
      # @param key [String, #to_s, nil]
      # @param item [::FFI::Pointer, #to_ptr]
      # @return [Integer]
      def insert(key, item)
        raise DestroyedError unless @ptr
        self_p = @ptr
        result = ::CZMQ::FFI.zhash_insert(self_p, key, item)
        result
      end

      # Update item into hash table with specified key and item.            
      # If key is already present, destroys old item and inserts new one.   
      # Use free_fn method to ensure deallocator is properly called on item.
      #
      # @param key [String, #to_s, nil]
      # @param item [::FFI::Pointer, #to_ptr]
      # @return [void]
      def update(key, item)
        raise DestroyedError unless @ptr
        self_p = @ptr
        result = ::CZMQ::FFI.zhash_update(self_p, key, item)
        result
      end

      # Remove an item specified by key from the hash table. If there was no such
      # item, this function does nothing.                                        
      #
      # @param key [String, #to_s, nil]
      # @return [void]
      def delete(key)
        raise DestroyedError unless @ptr
        self_p = @ptr
        result = ::CZMQ::FFI.zhash_delete(self_p, key)
        result
      end

      # Return the item at the specified key, or null
      #
      # @param key [String, #to_s, nil]
      # @return [::FFI::Pointer]
      def lookup(key)
        raise DestroyedError unless @ptr
        self_p = @ptr
        result = ::CZMQ::FFI.zhash_lookup(self_p, key)
        result
      end

      # Reindexes an item from an old key to a new key. If there was no such
      # item, does nothing. Returns 0 if successful, else -1.               
      #
      # @param old_key [String, #to_s, nil]
      # @param new_key [String, #to_s, nil]
      # @return [Integer]
      def rename(old_key, new_key)
        raise DestroyedError unless @ptr
        self_p = @ptr
        result = ::CZMQ::FFI.zhash_rename(self_p, old_key, new_key)
        result
      end

      # Set a free function for the specified hash table item. When the item is
      # destroyed, the free function, if any, is called on that item.          
      # Use this when hash items are dynamically allocated, to ensure that     
      # you don't have memory leaks. You can pass 'free' or NULL as a free_fn. 
      # Returns the item, or NULL if there is no such item.                    
      #
      # @param key [String, #to_s, nil]
      # @param free_fn [::FFI::Pointer, #to_ptr]
      # @return [::FFI::Pointer]
      def freefn(key, free_fn)
        raise DestroyedError unless @ptr
        self_p = @ptr
        result = ::CZMQ::FFI.zhash_freefn(self_p, key, free_fn)
        result
      end

      # Return the number of keys/items in the hash table
      #
      # @return [Integer]
      def size()
        raise DestroyedError unless @ptr
        self_p = @ptr
        result = ::CZMQ::FFI.zhash_size(self_p)
        result
      end

      # Make copy of hash table; if supplied table is null, returns null.    
      # Does not copy items themselves. Rebuilds new table so may be slow on 
      # very large tables. NOTE: only works with item values that are strings
      # since there's no other way to know how to duplicate the item value.  
      #
      # @return [Zhash]
      def dup()
        raise DestroyedError unless @ptr
        self_p = @ptr
        result = ::CZMQ::FFI.zhash_dup(self_p)
        result = Zhash.__new result, true
        result
      end

      # Return keys for items in table
      #
      # @return [Zlist]
      def keys()
        raise DestroyedError unless @ptr
        self_p = @ptr
        result = ::CZMQ::FFI.zhash_keys(self_p)
        result = Zlist.__new result, true
        result
      end

      # Simple iterator; returns first item in hash table, in no given order, 
      # or NULL if the table is empty. This method is simpler to use than the 
      # foreach() method, which is deprecated. To access the key for this item
      # use zhash_cursor(). NOTE: do NOT modify the table while iterating.    
      #
      # @return [::FFI::Pointer]
      def first()
        raise DestroyedError unless @ptr
        self_p = @ptr
        result = ::CZMQ::FFI.zhash_first(self_p)
        result
      end

      # Simple iterator; returns next item in hash table, in no given order, 
      # or NULL if the last item was already returned. Use this together with
      # zhash_first() to process all items in a hash table. If you need the  
      # items in sorted order, use zhash_keys() and then zlist_sort(). To    
      # access the key for this item use zhash_cursor(). NOTE: do NOT modify 
      # the table while iterating.                                           
      #
      # @return [::FFI::Pointer]
      def next()
        raise DestroyedError unless @ptr
        self_p = @ptr
        result = ::CZMQ::FFI.zhash_next(self_p)
        result
      end

      # After a successful first/next method, returns the key for the item that
      # was returned. This is a constant string that you may not modify or     
      # deallocate, and which lasts as long as the item in the hash. After an  
      # unsuccessful first/next, returns NULL.                                 
      #
      # @return [String]
      def cursor()
        raise DestroyedError unless @ptr
        self_p = @ptr
        result = ::CZMQ::FFI.zhash_cursor(self_p)
        result
      end

      # Add a comment to hash table before saving to disk. You can add as many   
      # comment lines as you like. These comment lines are discarded when loading
      # the file. If you use a null format, all comments are deleted.            
      #
      # @param format [String, #to_s, nil]
      # @param args [Array<Object>] see https://github.com/ffi/ffi/wiki/examples#using-varargs
      # @return [void]
      def comment(format, *args)
        raise DestroyedError unless @ptr
        self_p = @ptr
        result = ::CZMQ::FFI.zhash_comment(self_p, format, *args)
        result
      end

      # Serialize hash table to a binary frame that can be sent in a message.
      # The packed format is compatible with the 'dictionary' type defined in
      # http://rfc.zeromq.org/spec:35/FILEMQ, and implemented by zproto:     
      #                                                                      
      #    ; A list of name/value pairs                                      
      #    dictionary      = dict-count *( dict-name dict-value )            
      #    dict-count      = number-4                                        
      #    dict-value      = longstr                                         
      #    dict-name       = string                                          
      #                                                                      
      #    ; Strings are always length + text contents                       
      #    longstr         = number-4 *VCHAR                                 
      #    string          = number-1 *VCHAR                                 
      #                                                                      
      #    ; Numbers are unsigned integers in network byte order             
      #    number-1        = 1OCTET                                          
      #    number-4        = 4OCTET                                          
      #                                                                      
      # Comments are not included in the packed data. Item values MUST be    
      # strings.                                                             
      #
      # @return [Zframe]
      def pack()
        raise DestroyedError unless @ptr
        self_p = @ptr
        result = ::CZMQ::FFI.zhash_pack(self_p)
        result = Zframe.__new result, true
        result
      end

      # Save hash table to a text file in name=value format. Hash values must be
      # printable strings; keys may not contain '=' character. Returns 0 if OK, 
      # else -1 if a file error occurred.                                       
      #
      # @param filename [String, #to_s, nil]
      # @return [Integer]
      def save(filename)
        raise DestroyedError unless @ptr
        self_p = @ptr
        result = ::CZMQ::FFI.zhash_save(self_p, filename)
        result
      end

      # Load hash table from a text file in name=value format; hash table must 
      # already exist. Hash values must printable strings; keys may not contain
      # '=' character. Returns 0 if OK, else -1 if a file was not readable.    
      #
      # @param filename [String, #to_s, nil]
      # @return [Integer]
      def load(filename)
        raise DestroyedError unless @ptr
        self_p = @ptr
        result = ::CZMQ::FFI.zhash_load(self_p, filename)
        result
      end

      # When a hash table was loaded from a file by zhash_load, this method will
      # reload the file if it has been modified since, and is "stable", i.e. not
      # still changing. Returns 0 if OK, -1 if there was an error reloading the 
      # file.                                                                   
      #
      # @return [Integer]
      def refresh()
        raise DestroyedError unless @ptr
        self_p = @ptr
        result = ::CZMQ::FFI.zhash_refresh(self_p)
        result
      end

      # Set hash for automatic value destruction
      #
      # @return [void]
      def autofree()
        raise DestroyedError unless @ptr
        self_p = @ptr
        result = ::CZMQ::FFI.zhash_autofree(self_p)
        result
      end

      # DEPRECATED as clumsy -- use zhash_first/_next instead                  
      # Apply function to each item in the hash table. Items are iterated in no
      # defined order. Stops if callback function returns non-zero and returns 
      # final return code from callback function (zero = success).             
      # Callback function for zhash_foreach method                             
      #
      # @param callback [::FFI::Pointer, #to_ptr]
      # @param argument [::FFI::Pointer, #to_ptr]
      # @return [Integer]
      def foreach(callback, argument)
        raise DestroyedError unless @ptr
        self_p = @ptr
        result = ::CZMQ::FFI.zhash_foreach(self_p, callback, argument)
        result
      end

      # Self test of this class.
      #
      # @param verbose [Boolean]
      # @return [void]
      def self.test(verbose)
        verbose = !(0==verbose||!verbose) # boolean
        result = ::CZMQ::FFI.zhash_test(verbose)
        result
      end
    end
  end
end

################################################################################
#  THIS FILE IS 100% GENERATED BY ZPROJECT; DO NOT EDIT EXCEPT EXPERIMENTALLY  #
#  Please refer to the README for information about making permanent changes.  #
################################################################################
