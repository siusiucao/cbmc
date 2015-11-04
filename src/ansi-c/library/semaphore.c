/* FUNCTION: sem_init */

#include <semaphore.h>

inline int sem_init(sem_t *sem, int pshared, unsigned int value)
{
  __CPROVER_HIDE:;
  pshared;
  value;
  sem;
  __CPROVER_set_must(sem, "sem-init");
  __CPROVER_clear_may(sem, "sem-destroyed");
}

/* FUNCTION: sem_wait */

#include <semaphore.h>

inline int sem_wait(sem_t *sem)
{
  __CPROVER_HIDE:;
  sem;
  __CPROVER_assert(__CPROVER_get_must(sem, "sem-init"),
                   "semaphore must be initialized");
  __CPROVER_assert(!__CPROVER_get_may(sem, "sem-destroyed"),
                   "semaphore must not be destroyed");
}

/* FUNCTION: sem_timedwait */

#include <semaphore.h>

inline int sem_timedwait(sem_t *sem, const struct timespec *abstime)
{
  __CPROVER_HIDE:;
  sem;
  abstime;
  __CPROVER_assert(__CPROVER_get_must(sem, "sem-init"),
                   "semaphore must be initialized");
  __CPROVER_assert(!__CPROVER_get_may(sem, "sem-destroyed"),
                   "semaphore must not be destroyed");
}

/* FUNCTION: sem_trywait */

#include <semaphore.h>

inline int sem_trywait(sem_t *sem)
{
  __CPROVER_HIDE:;
  sem;
  __CPROVER_assert(__CPROVER_get_must(sem, "sem-init"),
                   "semaphore must be initialized");
  __CPROVER_assert(!__CPROVER_get_may(sem, "sem-destroyed"),
                   "semaphore must not be destroyed");
}

/* FUNCTION: sem_post */

#include <semaphore.h>

inline int sem_post(sem_t *sem)
{
  __CPROVER_HIDE:;
  sem;
  __CPROVER_assert(__CPROVER_get_must(sem, "sem-init"),
                   "semaphore must be initialized");
  __CPROVER_assert(!__CPROVER_get_may(sem, "sem-destroyed"),
                   "semaphore must not be destroyed");
}

/* FUNCTION: sem_post_multiple */

#include <semaphore.h>

inline int sem_post_multiple(sem_t *sem, int number)
{
  __CPROVER_HIDE:;
  sem;
  number;
  __CPROVER_assert(__CPROVER_get_must(sem, "sem-init"),
                   "semaphore must be initialized");
  __CPROVER_assert(!__CPROVER_get_may(sem, "sem-destroyed"),
                   "semaphore must not be destroyed");
}

/* FUNCTION: sem_getvalue */

#include <semaphore.h>

inline int sem_getvalue(sem_t *sem, int *sval)
{
  __CPROVER_HIDE:;
  sem;
  sval;
  __CPROVER_assert(__CPROVER_get_must(sem, "sem-init"),
                   "semaphore must be initialized");
  __CPROVER_assert(!__CPROVER_get_may(sem, "sem-destroyed"),
                   "semaphore must not be destroyed");
}

/* FUNCTION: sem_destroy */

#include <semaphore.h>

inline int sem_destroy(sem_t *sem)
{
  __CPROVER_HIDE:;
  sem;
  __CPROVER_assert(__CPROVER_get_must(sem, "sem-init"),
                   "semaphore must be initialized");
  __CPROVER_assert(!__CPROVER_get_may(sem, "sem-destroyed"),
                   "semaphore must not be destroyed");
  __CPROVER_set_may(sem, "sem-destroyed");
}
