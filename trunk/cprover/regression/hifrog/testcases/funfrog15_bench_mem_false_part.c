/*int nondet(void)
{
  int x;
  {
    return (x);
  }
  }*/


void error(void) 
{ 
// XXX Modified AEJ
  int foo;

  {
  goto ERROR;
  ERROR: ;
  return;
}
}

int m_run_st  ;
int m_run_i  ;
int m_run_pc  ;
int s_memory0  ;

int s_run_st  ;
int s_run_i  ;
int s_run_pc  ;
int c_m_lock  ;
int c_m_ev  ;
int c_req_type  ;
int c_req_a  ;
int c_req_d  ;
int c_rsp_type  ;
int c_rsp_status  ;
int c_rsp_d  ;
int c_empty_req  ;
int c_empty_rsp  ;
int c_read_req_ev  ;
int c_write_req_ev  ;
int c_read_rsp_ev  ;
int c_write_rsp_ev  ;
static int d_t  ;
static int a_t  ;
static int req_t_type  ;
static int req_t_a  ;
static int req_t_d  ;
static int rsp_t_type  ;
static int rsp_t_status  ;
static int rsp_t_d  ;
static int req_tt_type  ;
static int req_tt_a  ;
static int req_tt_d  ;
static int rsp_tt_type  ;
static int rsp_tt_status  ;
static int rsp_tt_d  ;

int s_memory_read(int i)
{
// XXX Modified AEJ
  int foo;
    int x;

  if (i==0)
    x = s_memory0;
  else
    error();

  return (x);
}

void s_memory_write(int i, int v)
{
// XXX Modified AEJ
  int foo;
    if (i==0)
    s_memory0 = v;
  else
    error();

  return;
}


void m_run(void) 
{ int d ;
  int a ;
  int req_type ;
  int req_a ;
  int req_d ;
  int rsp_type ;
  int rsp_status ;
  int rsp_d ;
  int req_type___0 ;
  int req_a___0 ;
  int req_d___0 ;
  int rsp_type___0 ;
  int rsp_status___0 ;
  int rsp_d___0 ;
// XXX Modified AEJ
  int foo;

  {
  if ((int )m_run_pc == 0) {
    goto L_MASTER_RUN_ENTRY;
  } else {
    if ((int )m_run_pc == 1) {
      goto L_MASTER_RUN_MUTEX;
    } else {
      if ((int )m_run_pc == 2) {
        goto L_MASTER_RUN_PUT;
      } else {
        if ((int )m_run_pc == 3) {
          goto L_MASTER_RUN_GET;
        } else {
          if ((int )m_run_pc == 4) {
            goto L_MASTER_RUN_MUTEX2;
          } else {
            if ((int )m_run_pc == 5) {
              goto L_MASTER_RUN_PUT2;
            } else {
              if ((int )m_run_pc == 6) {
                goto L_MASTER_RUN_GET2;
              } else {

              }
            }
          }
        }
      }
    }
  }
  L_MASTER_RUN_ENTRY: 
  a = 0;
  {
  if (1) {
    while_0_continue: /* CIL Label */ ;
    if (a < 1) {

    } else {
      goto while_0_break;
    }
    req_type = 1;
    req_a = a;
    req_d = a + 50;
    {
    if (1) {
      while_1_continue: /* CIL Label */ ;
      if (c_m_lock == 1) {

      } else {
        goto while_1_break;
      }
      m_run_st = 2;
      m_run_pc = 1;
      req_t_type = req_type;
      req_t_a = req_a;
      req_t_d = req_d;
      rsp_t_type = rsp_type;
      rsp_t_status = rsp_status;
      rsp_t_d = rsp_d;
      d_t = d;
      a_t = a;

      goto return_label;
      L_MASTER_RUN_MUTEX: 
      req_type = req_t_type;
      req_a = req_t_a;
      req_d = req_t_d;
      rsp_type = rsp_t_type;
      rsp_status = rsp_t_status;
      rsp_d = rsp_t_d;
      d = d_t;
      a = a_t;
    }
    while_1_break: /* CIL Label */ ;
    }
    c_m_lock = 1;
    {
    if (1) {
      while_2_continue: /* CIL Label */ ;
      if ((int )c_empty_req == 0) {

      } else {
        goto while_2_break;
      }
      m_run_st = 2;
      m_run_pc = 2;
      req_t_type = req_type;
      req_t_a = req_a;
      req_t_d = req_d;
      rsp_t_type = rsp_type;
      rsp_t_status = rsp_status;
      rsp_t_d = rsp_d;
      d_t = d;
      a_t = a;

      goto return_label;
      L_MASTER_RUN_PUT: 
      req_type = req_t_type;
      req_a = req_t_a;
      req_d = req_t_d;
      rsp_type = rsp_t_type;
      rsp_status = rsp_t_status;
      rsp_d = rsp_t_d;
      a = a_t;
      d = d_t;
    }
    while_2_break: /* CIL Label */ ;
    }
    c_req_type = req_type;
    c_req_a = req_a;
    c_req_d = req_d;
    c_empty_req = 0;
    c_write_req_ev = 1;
    if ((int )m_run_pc == 1) {
      if ((int )c_m_ev == 1) {
        m_run_st = 0;
      } else {
        goto _L___3;
      }
    } else {
      _L___3: /* CIL Label */ 
      if ((int )m_run_pc == 2) {
        if ((int )c_read_req_ev == 1) {
          m_run_st = 0;
        } else {
          goto _L___2;
        }
      } else {
        _L___2: /* CIL Label */ 
        if ((int )m_run_pc == 3) {
          if ((int )c_write_rsp_ev == 1) {
            m_run_st = 0;
          } else {
            goto _L___1;
          }
        } else {
          _L___1: /* CIL Label */ 
          if ((int )m_run_pc == 4) {
            if ((int )c_m_ev == 1) {
              m_run_st = 0;
            } else {
              goto _L___0;
            }
          } else {
            _L___0: /* CIL Label */ 
            if ((int )m_run_pc == 5) {
              if ((int )c_read_req_ev == 1) {
                m_run_st = 0;
              } else {
                goto _L;
              }
            } else {
              _L: /* CIL Label */ 
              if ((int )m_run_pc == 6) {
                if ((int )c_write_rsp_ev == 1) {
                  m_run_st = 0;
                } else {

                }
              } else {

              }
            }
          }
        }
      }
    }
    if ((int )s_run_pc == 2) {
      if ((int )c_write_req_ev == 1) {
        s_run_st = 0;
      } else {
        goto _L___4;
      }
    } else {
      _L___4: /* CIL Label */ 
      if ((int )s_run_pc == 1) {
        if ((int )c_read_rsp_ev == 1) {
          s_run_st = 0;
        } else {

        }
      } else {

      }
    }
    c_write_req_ev = 2;
    {
    if (1) {
      while_3_continue: /* CIL Label */ ;
      if ((int )c_empty_rsp == 1) {

      } else {
        goto while_3_break;
      }
      m_run_st = 2;
      m_run_pc = 3;
      req_t_type = req_type;
      req_t_a = req_a;
      req_t_d = req_d;
      rsp_t_type = rsp_type;
      rsp_t_status = rsp_status;
      rsp_t_d = rsp_d;
      d_t = d;
      a_t = a;

      goto return_label;
      L_MASTER_RUN_GET: 
      req_type = req_t_type;
      req_a = req_t_a;
      req_d = req_t_d;
      rsp_type = rsp_t_type;
      rsp_status = rsp_t_status;
      rsp_d = rsp_t_d;
      d = d_t;
      a = a_t;
    }
    while_3_break: /* CIL Label */ ;
    }
    rsp_type = c_rsp_type;
    rsp_status = c_rsp_status;
    rsp_d = c_rsp_d;
    c_empty_rsp = 1;
    c_read_rsp_ev = 1;
    if ((int )m_run_pc == 1) {
      if ((int )c_m_ev == 1) {
        m_run_st = 0;
      } else {
        goto _L___9;
      }
    } else {
      _L___9: /* CIL Label */ 
      if ((int )m_run_pc == 2) {
        if ((int )c_read_req_ev == 1) {
          m_run_st = 0;
        } else {
          goto _L___8;
        }
      } else {
        _L___8: /* CIL Label */ 
        if ((int )m_run_pc == 3) {
          if ((int )c_write_rsp_ev == 1) {
            m_run_st = 0;
          } else {
            goto _L___7;
          }
        } else {
          _L___7: /* CIL Label */ 
          if ((int )m_run_pc == 4) {
            if ((int )c_m_ev == 1) {
              m_run_st = 0;
            } else {
              goto _L___6;
            }
          } else {
            _L___6: /* CIL Label */ 
            if ((int )m_run_pc == 5) {
              if ((int )c_read_req_ev == 1) {
                m_run_st = 0;
              } else {
                goto _L___5;
              }
            } else {
              _L___5: /* CIL Label */ 
              if ((int )m_run_pc == 6) {
                if ((int )c_write_rsp_ev == 1) {
                  m_run_st = 0;
                } else {

                }
              } else {

              }
            }
          }
        }
      }
    }
    if ((int )s_run_pc == 2) {
      if ((int )c_write_req_ev == 1) {
        s_run_st = 0;
      } else {
        goto _L___10;
      }
    } else {
      _L___10: /* CIL Label */ 
      if ((int )s_run_pc == 1) {
        if ((int )c_read_rsp_ev == 1) {
          s_run_st = 0;
        } else {

        }
      } else {

      }
    }
    c_read_rsp_ev = 2;
    if (c_m_lock == 0) {
      {
      error();
      }
    } else {

    }
    c_m_lock = 0;
    c_m_ev = 1;
    if ((int )m_run_pc == 1) {
      if ((int )c_m_ev == 1) {
        m_run_st = 0;
      } else {
        goto _L___15;
      }
    } else {
      _L___15: /* CIL Label */ 
      if ((int )m_run_pc == 2) {
        if ((int )c_read_req_ev == 1) {
          m_run_st = 0;
        } else {
          goto _L___14;
        }
      } else {
        _L___14: /* CIL Label */ 
        if ((int )m_run_pc == 3) {
          if ((int )c_write_rsp_ev == 1) {
            m_run_st = 0;
          } else {
            goto _L___13;
          }
        } else {
          _L___13: /* CIL Label */ 
          if ((int )m_run_pc == 4) {
            if ((int )c_m_ev == 1) {
              m_run_st = 0;
            } else {
              goto _L___12;
            }
          } else {
            _L___12: /* CIL Label */ 
            if ((int )m_run_pc == 5) {
              if ((int )c_read_req_ev == 1) {
                m_run_st = 0;
              } else {
                goto _L___11;
              }
            } else {
              _L___11: /* CIL Label */ 
              if ((int )m_run_pc == 6) {
                if ((int )c_write_rsp_ev == 1) {
                  m_run_st = 0;
                } else {

                }
              } else {

              }
            }
          }
        }
      }
    }
    if ((int )s_run_pc == 2) {
      if ((int )c_write_req_ev == 1) {
        s_run_st = 0;
      } else {
        goto _L___16;
      }
    } else {
      _L___16: /* CIL Label */ 
      if ((int )s_run_pc == 1) {
        if ((int )c_read_rsp_ev == 1) {
          s_run_st = 0;
        } else {

        }
      } else {

      }
    }
    c_m_ev = 2;
    a += 1;
  }
  while_0_break: /* CIL Label */ ;
  }
  a = 0;
  {
  if (1) {
    while_4_continue: /* CIL Label */ ;
    if (a < 1) {

    } else {
      goto while_4_break;
    }
    req_type___0 = 0;
    req_a___0 = a;
    {
    if (1) {
      while_5_continue: /* CIL Label */ ;
      if (c_m_lock == 1) {

      } else {
        goto while_5_break;
      }
      m_run_st = 2;
      m_run_pc = 4;
      req_tt_type = req_type___0;
      req_tt_a = req_a___0;
      req_tt_d = req_d___0;
      rsp_tt_type = rsp_type___0;
      rsp_tt_status = rsp_status___0;
      rsp_tt_d = rsp_d___0;
      d_t = d;
      a_t = a;

      goto return_label;
      L_MASTER_RUN_MUTEX2: 
      req_type___0 = req_tt_type;
      req_a___0 = req_tt_a;
      req_d___0 = req_tt_d;
      rsp_type___0 = rsp_tt_type;
      rsp_status___0 = rsp_tt_status;
      rsp_d___0 = rsp_tt_d;
      d = d_t;
      a = a_t;
    }
    while_5_break: /* CIL Label */ ;
    }
    c_m_lock = 1;
    {
    if (1) {
      while_6_continue: /* CIL Label */ ;
      if ((int )c_empty_req == 0) {

      } else {
        goto while_6_break;
      }
      m_run_st = 2;
      m_run_pc = 5;
      req_tt_type = req_type___0;
      req_tt_a = req_a___0;
      req_tt_d = req_d___0;
      rsp_tt_type = rsp_type___0;
      rsp_tt_status = rsp_status___0;
      rsp_tt_d = rsp_d___0;
      d_t = d;
      a_t = a;

      goto return_label;
      L_MASTER_RUN_PUT2: 
      req_type___0 = req_tt_type;
      req_a___0 = req_tt_a;
      req_d___0 = req_tt_d;
      rsp_type___0 = rsp_tt_type;
      rsp_status___0 = rsp_tt_status;
      rsp_d___0 = rsp_tt_d;
      d = d_t;
      a = a_t;
    }
    while_6_break: /* CIL Label */ ;
    }
    c_req_type = req_type___0;
    c_req_a = req_a___0;
    c_req_d = req_d___0;
    c_empty_req = 0;
    c_write_req_ev = 1;
    if ((int )m_run_pc == 1) {
      if ((int )c_m_ev == 1) {
        m_run_st = 0;
      } else {
        goto _L___21;
      }
    } else {
      _L___21: /* CIL Label */ 
      if ((int )m_run_pc == 2) {
        if ((int )c_read_req_ev == 1) {
          m_run_st = 0;
        } else {
          goto _L___20;
        }
      } else {
        _L___20: /* CIL Label */ 
        if ((int )m_run_pc == 3) {
          if ((int )c_write_rsp_ev == 1) {
            m_run_st = 0;
          } else {
            goto _L___19;
          }
        } else {
          _L___19: /* CIL Label */ 
          if ((int )m_run_pc == 4) {
            if ((int )c_m_ev == 1) {
              m_run_st = 0;
            } else {
              goto _L___18;
            }
          } else {
            _L___18: /* CIL Label */ 
            if ((int )m_run_pc == 5) {
              if ((int )c_read_req_ev == 1) {
                m_run_st = 0;
              } else {
                goto _L___17;
              }
            } else {
              _L___17: /* CIL Label */ 
              if ((int )m_run_pc == 6) {
                if ((int )c_write_rsp_ev == 1) {
                  m_run_st = 0;
                } else {

                }
              } else {

              }
            }
          }
        }
      }
    }
    if ((int )s_run_pc == 2) {
      if ((int )c_write_req_ev == 1) {
        s_run_st = 0;
      } else {
        goto _L___22;
      }
    } else {
      _L___22: /* CIL Label */ 
      if ((int )s_run_pc == 1) {
        if ((int )c_read_rsp_ev == 1) {
          s_run_st = 0;
        } else {

        }
      } else {

      }
    }
    c_write_req_ev = 2;
    {
    if (1) {
      while_7_continue: /* CIL Label */ ;
      if ((int )c_empty_rsp == 1) {

      } else {
        goto while_7_break;
      }
      m_run_st = 2;
      m_run_pc = 6;
      req_tt_type = req_type___0;
      req_tt_a = req_a___0;
      req_tt_d = req_d___0;
      rsp_tt_type = rsp_type___0;
      rsp_tt_status = rsp_status___0;
      rsp_tt_d = rsp_d___0;
      d_t = d;
      a_t = a;

      goto return_label;
      L_MASTER_RUN_GET2: 
      req_type___0 = req_tt_type;
      req_a___0 = req_tt_a;
      req_d___0 = req_tt_d;
      rsp_type___0 = rsp_tt_type;
      rsp_status___0 = rsp_tt_status;
      rsp_d___0 = rsp_tt_d;
      d = d_t;
      a = a_t;
    }
    while_7_break: /* CIL Label */ ;
    }
    rsp_type___0 = c_rsp_type;
    rsp_status___0 = c_rsp_status;
    rsp_d___0 = c_rsp_d;
    c_empty_rsp = 1;
    c_read_rsp_ev = 1;
    if ((int )m_run_pc == 1) {
      if ((int )c_m_ev == 1) {
        m_run_st = 0;
      } else {
        goto _L___27;
      }
    } else {
      _L___27: /* CIL Label */ 
      if ((int )m_run_pc == 2) {
        if ((int )c_read_req_ev == 1) {
          m_run_st = 0;
        } else {
          goto _L___26;
        }
      } else {
        _L___26: /* CIL Label */ 
        if ((int )m_run_pc == 3) {
          if ((int )c_write_rsp_ev == 1) {
            m_run_st = 0;
          } else {
            goto _L___25;
          }
        } else {
          _L___25: /* CIL Label */ 
          if ((int )m_run_pc == 4) {
            if ((int )c_m_ev == 1) {
              m_run_st = 0;
            } else {
              goto _L___24;
            }
          } else {
            _L___24: /* CIL Label */ 
            if ((int )m_run_pc == 5) {
              if ((int )c_read_req_ev == 1) {
                m_run_st = 0;
              } else {
                goto _L___23;
              }
            } else {
              _L___23: /* CIL Label */ 
              if ((int )m_run_pc == 6) {
                if ((int )c_write_rsp_ev == 1) {
                  m_run_st = 0;
                } else {

                }
              } else {

              }
            }
          }
        }
      }
    }
    if ((int )s_run_pc == 2) {
      if ((int )c_write_req_ev == 1) {
        s_run_st = 0;
      } else {
        goto _L___28;
      }
    } else {
      _L___28: /* CIL Label */ 
      if ((int )s_run_pc == 1) {
        if ((int )c_read_rsp_ev == 1) {
          s_run_st = 0;
        } else {

        }
      } else {

      }
    }
    c_read_rsp_ev = 2;
    if (c_m_lock == 0) {
      {
      error();
      }
    } else {

    }
    c_m_lock = 0;
    c_m_ev = 1;
    if ((int )m_run_pc == 1) {
      if ((int )c_m_ev == 1) {
        m_run_st = 0;
      } else {
        goto _L___33;
      }
    } else {
      _L___33: /* CIL Label */ 
      if ((int )m_run_pc == 2) {
        if ((int )c_read_req_ev == 1) {
          m_run_st = 0;
        } else {
          goto _L___32;
        }
      } else {
        _L___32: /* CIL Label */ 
        if ((int )m_run_pc == 3) {
          if ((int )c_write_rsp_ev == 1) {
            m_run_st = 0;
          } else {
            goto _L___31;
          }
        } else {
          _L___31: /* CIL Label */ 
          if ((int )m_run_pc == 4) {
            if ((int )c_m_ev == 1) {
              m_run_st = 0;
            } else {
              goto _L___30;
            }
          } else {
            _L___30: /* CIL Label */ 
            if ((int )m_run_pc == 5) {
              if ((int )c_read_req_ev == 1) {
                m_run_st = 0;
              } else {
                goto _L___29;
              }
            } else {
              _L___29: /* CIL Label */ 
              if ((int )m_run_pc == 6) {
                if ((int )c_write_rsp_ev == 1) {
                  m_run_st = 0;
                } else {

                }
              } else {

              }
            }
          }
        }
      }
    }
    if ((int )s_run_pc == 2) {
      if ((int )c_write_req_ev == 1) {
        s_run_st = 0;
      } else {
        goto _L___34;
      }
    } else {
      _L___34: /* CIL Label */ 
      if ((int )s_run_pc == 1) {
        if ((int )c_read_rsp_ev == 1) {
          s_run_st = 0;
        } else {

        }
      } else {

      }
    }
    c_m_ev = 2;
    if (! (req_a___0 + 50 == rsp_d___0)) {
      {
      error();
      }
    } else {

    }
    a += 1;
  }
  while_4_break: /* CIL Label */ ;
  }

  return_label: /* CIL Label */ 
  return;
}
}
static int req_t_type___0  ;
static int req_t_a___0  ;
static int req_t_d___0  ;
static int rsp_t_type___0  ;
static int rsp_t_status___0  ;
static int rsp_t_d___0  ;
void s_run(void) 
{ int req_type ;
  int req_a ;
  int req_d ;
  int rsp_type ;
  int rsp_status ;
  int rsp_d ;
  int dummy ;
// XXX Modified AEJ
  int foo;

  {
  if ((int )s_run_pc == 0) {
    goto L_SLAVE_RUN_ENTRY;
  } else {
    if ((int )s_run_pc == 1) {
      goto L_SLAVE_RUN_PUT;
    } else {
      if ((int )s_run_pc == 2) {
        goto L_SLAVE_RUN_GET;
      } else {

      }
    }
  }
  L_SLAVE_RUN_ENTRY: 
  {
  if (1) {
    while_8_continue: /* CIL Label */ ;
    {
    if (1) {
      while_9_continue: /* CIL Label */ ;
      if ((int )c_empty_req == 1) {

      } else {
        goto while_9_break;
      }
      s_run_st = 2;
      s_run_pc = 2;
      req_t_type___0 = req_type;
      req_t_a___0 = req_a;
      req_t_d___0 = req_d;
      rsp_t_type___0 = rsp_type;
      rsp_t_status___0 = rsp_status;
      rsp_t_d___0 = rsp_d;

      goto return_label;
      L_SLAVE_RUN_GET: 
      req_type = req_t_type___0;
      req_a = req_t_a___0;
      req_d = req_t_d___0;
      rsp_type = rsp_t_type___0;
      rsp_status = rsp_t_status___0;
      rsp_d = rsp_t_d___0;
    }
    while_9_break: /* CIL Label */ ;
    }
    req_type = c_req_type;
    req_a = c_req_a;
    req_d = c_req_d;
    c_empty_req = 1;
    c_read_req_ev = 1;
    if ((int )m_run_pc == 1) {
      if ((int )c_m_ev == 1) {
        m_run_st = 0;
      } else {
        goto _L___3;
      }
    } else {
      _L___3: /* CIL Label */ 
      if ((int )m_run_pc == 2) {
        if ((int )c_read_req_ev == 1) {
          m_run_st = 0;
        } else {
          goto _L___2;
        }
      } else {
        _L___2: /* CIL Label */ 
        if ((int )m_run_pc == 3) {
          if ((int )c_write_rsp_ev == 1) {
            m_run_st = 0;
          } else {
            goto _L___1;
          }
        } else {
          _L___1: /* CIL Label */ 
          if ((int )m_run_pc == 4) {
            if ((int )c_m_ev == 1) {
              m_run_st = 0;
            } else {
              goto _L___0;
            }
          } else {
            _L___0: /* CIL Label */ 
            if ((int )m_run_pc == 5) {
              if ((int )c_read_req_ev == 1) {
                m_run_st = 0;
              } else {
                goto _L;
              }
            } else {
              _L: /* CIL Label */ 
              if ((int )m_run_pc == 6) {
                if ((int )c_write_rsp_ev == 1) {
                  m_run_st = 0;
                } else {

                }
              } else {

              }
            }
          }
        }
      }
    }
    if ((int )s_run_pc == 2) {
      if ((int )c_write_req_ev == 1) {
        s_run_st = 0;
      } else {
        goto _L___4;
      }
    } else {
      _L___4: /* CIL Label */ 
      if ((int )s_run_pc == 1) {
        if ((int )c_read_rsp_ev == 1) {
          s_run_st = 0;
        } else {

        }
      } else {

      }
    }
    c_read_req_ev = 2;
    rsp_type = req_type;
    if ((int )req_type == 0) {

      rsp_d = s_memory_read(req_a);

      rsp_status = 1;
    } else {
      if ((int )req_type == 1) {

	s_memory_write(req_a,req_d);

        rsp_status = 1;
      } else {
        rsp_status = 0;
      }
    }
    {
    if (1) {
      while_10_continue: /* CIL Label */ ;
      if ((int )c_empty_rsp == 0) {

      } else {
        goto while_10_break;
      }
      s_run_st = 2;
      s_run_pc = 1;
      req_t_type___0 = req_type;
      req_t_a___0 = req_a;
      req_t_d___0 = req_d;
      rsp_t_type___0 = rsp_type;
      rsp_t_status___0 = rsp_status;
      rsp_t_d___0 = rsp_d;

      goto return_label;
      L_SLAVE_RUN_PUT: 
      req_type = req_t_type___0;
      req_a = req_t_a___0;
      req_d = req_t_d___0;
      rsp_type = rsp_t_type___0;
      rsp_status = rsp_t_status___0;
      rsp_d = rsp_t_d___0;
    }
    while_10_break: /* CIL Label */ ;
    }
    c_rsp_type = rsp_type;
    c_rsp_status = rsp_status;
    c_rsp_d = rsp_d;
    c_empty_rsp = 0;
    c_write_rsp_ev = 1;
    if ((int )m_run_pc == 1) {
      if ((int )c_m_ev == 1) {
        m_run_st = 0;
      } else {
        goto _L___9;
      }
    } else {
      _L___9: /* CIL Label */ 
      if ((int )m_run_pc == 2) {
        if ((int )c_read_req_ev == 1) {
          m_run_st = 0;
        } else {
          goto _L___8;
        }
      } else {
        _L___8: /* CIL Label */ 
        if ((int )m_run_pc == 3) {
          if ((int )c_write_rsp_ev == 1) {
            m_run_st = 0;
          } else {
            goto _L___7;
          }
        } else {
          _L___7: /* CIL Label */ 
          if ((int )m_run_pc == 4) {
            if ((int )c_m_ev == 1) {
              m_run_st = 0;
            } else {
              goto _L___6;
            }
          } else {
            _L___6: /* CIL Label */ 
            if ((int )m_run_pc == 5) {
              if ((int )c_read_req_ev == 1) {
                m_run_st = 0;
              } else {
                goto _L___5;
              }
            } else {
              _L___5: /* CIL Label */ 
              if ((int )m_run_pc == 6) {
                if ((int )c_write_rsp_ev == 1) {
                  m_run_st = 0;
                } else {

                }
              } else {

              }
            }
          }
        }
      }
    }
    if ((int )s_run_pc == 2) {
      if ((int )c_write_req_ev == 1) {
        s_run_st = 0;
      } else {
        goto _L___10;
      }
    } else {
      _L___10: /* CIL Label */ 
      if ((int )s_run_pc == 1) {
        if ((int )c_read_rsp_ev == 1) {
          s_run_st = 0;
        } else {

        }
      } else {

      }
    }
    c_write_rsp_ev = 2;
  }
  while_8_break: /* CIL Label */ ;
  }
  return_label: /* CIL Label */ 
  return;
}
}
void eval(void) 
{ int tmp ;
  int tmp___0 ;
// XXX Modified AEJ
  int nondet_int(); 
//  int nondet_int() { int foo; return foo; }
// XXX Modified AEJ
  int foo;

  {
  {
  if (1) {
    while_11_continue: /* CIL Label */ ;
    if ((int )m_run_st == 0) {

    } else {
      if ((int )s_run_st == 0) {

      } else {
        goto while_11_break;
      }
    }
    if ((int )m_run_st == 0) {
      {
	tmp = nondet_int();
      }
      if (tmp) {
        {
        m_run_st = 1;
        m_run();
        }
      } else {

      }
    } else {

    }
    if ((int )s_run_st == 0) {
      {
	tmp___0 = nondet_int();
      }
      if (tmp___0) {
        {
        s_run_st = 1;
        s_run();
        }
      } else {

      }
    } else {

    }
  }
  while_11_break: /* CIL Label */ ;
  }

  return;
}
}
void start_simulation(void) 
{ int kernel_st ;
// XXX Modified AEJ
  int foo;
assert(c_m_ev == c_write_rsp_ev);
assert(a_t == 0);
assert(store(s_memory0));
assert(store(m_run_i));
assert(a_t == req_t_a);
assert(store(d_t));
assert(c_m_ev == c_write_req_ev);
assert(c_empty_req == 1);
assert(a_t == rsp_tt_d);
assert(a_t == rsp_t_type);
assert(a_t == rsp_t_d);
assert(store(s_run_i));
assert(a_t == m_run_pc);
assert(a_t == s_run_pc);
assert(store(c_write_rsp_ev));
assert(c_empty_req == m_run_i);
assert(a_t == c_req_d);
assert(store(req_tt_a));
assert(a_t == m_run_st);
assert(store(c_write_req_ev));
assert(a_t == rsp_t_status);
assert(store(c_m_lock));
assert(a_t == req_t_a___0);
assert(store(rsp_t_status___0));
assert(store(m_run_pc));
assert(store(c_empty_req));
assert(a_t == c_req_type);
assert(a_t == c_rsp_status);
assert(a_t == rsp_t_d___0);
assert(a_t == c_m_lock);
assert(a_t == s_memory0);
assert(store(rsp_t_d));
assert(store(rsp_t_type));
assert(a_t == c_req_a);
assert(a_t == rsp_tt_type);
assert(store(req_tt_type));
assert(a_t == s_run_st);
assert(store(rsp_t_d___0));
assert(store(req_t_d___0));
assert(store(rsp_t_status));
assert(store(req_tt_d));
assert(store(req_t_type));
assert(store(c_req_d));
assert(store(c_rsp_status));
assert(a_t == req_t_d);
assert(store(rsp_t_type___0));
assert(store(req_t_type___0));
assert(a_t == rsp_t_status___0);
assert(a_t == req_tt_type);
assert(store(s_run_st));
assert(store(s_run_pc));
assert(store(req_t_a));
assert(c_empty_req == c_empty_rsp);
assert(store(c_m_ev));
assert(a_t == req_tt_d);
assert(a_t == d_t);
assert(store(rsp_tt_d));
assert(store(c_rsp_type));
assert(store(rsp_tt_type));
assert(a_t == req_tt_a);
assert(a_t == c_rsp_type);
assert(a_t == rsp_tt_status);
assert(c_empty_req == s_run_i);
assert(store(c_read_rsp_ev));
assert(a_t == req_t_type___0);
assert(store(c_req_type));
assert(c_m_ev == c_read_rsp_ev);
assert(a_t == req_t_type);
assert(c_m_ev == c_read_req_ev);
assert(store(req_t_a___0));
assert(store(rsp_tt_status));
assert(a_t == req_t_d___0);
assert(store(req_t_d));
assert(store(c_read_req_ev));
assert(store(m_run_st));
assert(a_t == c_rsp_d);
assert(c_m_ev == 2);
assert(store(c_empty_rsp));
assert(store(c_req_a));
assert(store(a_t));
assert(a_t == rsp_t_type___0);
assert(store(c_rsp_d));
  {
  kernel_st = 0;
  if ((int )m_run_i == 1) {
    m_run_st = 0;
  } else {
    m_run_st = 2;
  }
  if ((int )s_run_i == 1) {
    s_run_st = 0;
  } else {
    s_run_st = 2;
  }
  if ((int )m_run_pc == 1) {
    if ((int )c_m_ev == 1) {
      m_run_st = 0;
    } else {
      goto _L___3;
    }
  } else {
    _L___3: /* CIL Label */ 
    if ((int )m_run_pc == 2) {
      if ((int )c_read_req_ev == 1) {
        m_run_st = 0;
      } else {
        goto _L___2;
      }
    } else {
      _L___2: /* CIL Label */ 
      if ((int )m_run_pc == 3) {
        if ((int )c_write_rsp_ev == 1) {
          m_run_st = 0;
        } else {
          goto _L___1;
        }
      } else {
        _L___1: /* CIL Label */ 
        if ((int )m_run_pc == 4) {
          if ((int )c_m_ev == 1) {
            m_run_st = 0;
          } else {
            goto _L___0;
          }
        } else {
          _L___0: /* CIL Label */ 
          if ((int )m_run_pc == 5) {
            if ((int )c_read_req_ev == 1) {
              m_run_st = 0;
            } else {
              goto _L;
            }
          } else {
            _L: /* CIL Label */ 
            if ((int )m_run_pc == 6) {
              if ((int )c_write_rsp_ev == 1) {
                m_run_st = 0;
              } else {

              }
            } else {

            }
          }
        }
      }
    }
  }
  if ((int )s_run_pc == 2) {
    if ((int )c_write_req_ev == 1) {
      s_run_st = 0;
    } else {
      goto _L___4;
    }
  } else {
    _L___4: /* CIL Label */ 
    if ((int )s_run_pc == 1) {
      if ((int )c_read_rsp_ev == 1) {
        s_run_st = 0;
      } else {

      }
    } else {

    }
  }
  {
int __retres1 ;
  if (1) {
    while_12_continue: /* CIL Label */ ;
    {
    kernel_st = 1;
    eval();
    }
    kernel_st = 2;
    kernel_st = 3;
    if ((int )m_run_pc == 1) {
      if ((int )c_m_ev == 1) {
        m_run_st = 0;
      } else {
        goto _L___9;
      }
    } else {
      _L___9: /* CIL Label */ 
      if ((int )m_run_pc == 2) {
        if ((int )c_read_req_ev == 1) {
          m_run_st = 0;
        } else {
          goto _L___8;
        }
      } else {
        _L___8: /* CIL Label */ 
        if ((int )m_run_pc == 3) {
          if ((int )c_write_rsp_ev == 1) {
            m_run_st = 0;
          } else {
//assert(__retres1 == rsp_t_type___0);
//assert(__retres1 == rsp_tt_d);
//assert(__retres1 == req_tt_a);
//assert(__retres1 == s_run_pc);
//assert(__retres1 == rsp_t_d);
//assert(__retres1 == req_tt_type);
//assert(__retres1 == m_run_pc);
assert(m_run_i == s_run_i);
//assert(__retres1 == c_rsp_status);
//assert(__retres1 == req_tt_d);
assert(m_run_i == 1);
//assert(__retres1 == c_rsp_d);
//assert(__retres1 == c_write_req_ev);
//assert(__retres1 == rsp_t_d___0);
//assert(__retres1 == c_rsp_type);
//assert(__retres1 == c_empty_req);
//assert(__retres1 == d_t);
//assert(__retres1 == req_t_a);
//assert(__retres1 == rsp_t_status___0);
//assert(__retres1 == req_t_a___0);
//assert(__retres1 == rsp_tt_type);
//assert(__retres1 == rsp_t_type);
//assert(__retres1 == req_t_d);
//assert(__retres1 == req_t_d___0);
//assert(__retres1 == rsp_t_status);
//assert(__retres1 == c_req_a);
//assert(__retres1 == c_req_type);
//assert(__retres1 == c_req_d);
//assert(__retres1 == s_run_st);
//assert(__retres1 == a_t);
//assert(__retres1 == 0);
//assert(__retres1 == c_empty_rsp);
//assert(__retres1 == c_m_lock);
//assert(__retres1 == req_t_type___0);
//assert(__retres1 == c_write_rsp_ev);
//assert(__retres1 == req_t_type);
//assert(__retres1 == c_read_req_ev);
//assert(__retres1 == m_run_st);
//assert(__retres1 == s_memory0);
assert(c_m_ev == 2);
//assert(__retres1 == c_read_rsp_ev);
            goto _L___7;
//assert(__retres1 == rsp_t_type___0);
//assert(__retres1 == rsp_tt_d);
//assert(__retres1 == req_tt_a);
//assert(__retres1 == s_run_pc);
//assert(__retres1 == rsp_t_d);
//assert(__retres1 == req_tt_type);
//assert(__retres1 == m_run_pc);
assert(m_run_i == s_run_i);
//assert(__retres1 == c_rsp_status);
//assert(__retres1 == req_tt_d);
assert(m_run_i == 1);
//assert(__retres1 == c_rsp_d);
//assert(__retres1 == c_write_req_ev);
//assert(__retres1 == rsp_t_d___0);
//assert(__retres1 == c_rsp_type);
//assert(__retres1 == c_empty_req);
//assert(__retres1 == d_t);
//assert(__retres1 == req_t_a);
//assert(__retres1 == rsp_t_status___0);
//assert(__retres1 == req_t_a___0);
//assert(__retres1 == rsp_tt_type);
//assert(__retres1 == rsp_t_type);
//assert(__retres1 == req_t_d);
//assert(__retres1 == req_t_d___0);
//assert(__retres1 == rsp_t_status);
//assert(__retres1 == c_req_a);
//assert(__retres1 == c_req_type);
//assert(__retres1 == c_req_d);
//assert(__retres1 == s_run_st);
//assert(__retres1 == a_t);
//assert(__retres1 == 0);
//assert(__retres1 == c_empty_rsp);
//assert(__retres1 == c_m_lock);
//assert(__retres1 == req_t_type___0);
//assert(__retres1 == c_write_rsp_ev);
//assert(__retres1 == req_t_type);
//assert(__retres1 == c_read_req_ev);
//assert(__retres1 == m_run_st);
//assert(__retres1 == s_memory0);
assert(c_m_ev == 2);
//assert(__retres1 == c_read_rsp_ev);
          }
//assert(__retres1 == rsp_t_type___0);
//assert(__retres1 == rsp_tt_d);
//assert(__retres1 == req_tt_a);
//assert(__retres1 == s_run_pc);
//assert(__retres1 == rsp_t_d);
//assert(__retres1 == req_tt_type);
//assert(__retres1 == m_run_pc);
assert(c_empty_req == 1);
//assert(__retres1 == c_rsp_status);
//assert(__retres1 == req_tt_d);
//assert(__retres1 == c_rsp_d);
//assert(__retres1 == c_write_req_ev);
//assert(__retres1 == rsp_t_d___0);
//assert(__retres1 == c_rsp_type);
//assert(__retres1 == d_t);
//assert(__retres1 == req_t_a);
assert(c_empty_req == m_run_i);
//assert(__retres1 == rsp_t_status___0);
//assert(__retres1 == req_t_a___0);
//assert(__retres1 == rsp_tt_type);
//assert(__retres1 == rsp_t_type);
//assert(__retres1 == req_t_d);
//assert(__retres1 == req_t_d___0);
//assert(__retres1 == rsp_t_status);
assert(c_empty_req == s_run_i);
//assert(__retres1 == c_req_a);
//assert(__retres1 == c_req_type);
//assert(__retres1 == c_req_d);
//assert(__retres1 == s_run_st);
//assert(__retres1 == a_t);
//assert(__retres1 == 0);
//assert(__retres1 == c_empty_rsp);
//assert(__retres1 == c_m_lock);
//assert(__retres1 == req_t_type___0);
//assert(__retres1 == c_write_rsp_ev);
//assert(__retres1 == req_t_type);
//assert(__retres1 == c_read_req_ev);
//assert(__retres1 == m_run_st);
//assert(__retres1 == s_memory0);
assert(c_m_ev == 2);
//assert(__retres1 == c_read_rsp_ev);
        } else {
//assert(__retres1 == rsp_t_type___0);
//assert(__retres1 == rsp_tt_d);
//assert(__retres1 == req_tt_a);
//assert(__retres1 == s_run_pc);
//assert(__retres1 == rsp_t_d);
//assert(__retres1 == m_run_pc);
//assert(__retres1 == req_tt_type);
assert(c_empty_req == 1);
//assert(__retres1 == c_rsp_status);
//assert(__retres1 == req_tt_d);
//assert(__retres1 == c_rsp_d);
//assert(__retres1 == c_write_req_ev);
//assert(__retres1 == rsp_t_d___0);
//assert(__retres1 == c_rsp_type);
//assert(__retres1 == d_t);
assert(c_empty_req == c_empty_rsp);
//assert(__retres1 == req_t_a);
assert(c_empty_req == m_run_i);
//assert(__retres1 == rsp_t_status___0);
//assert(__retres1 == req_t_a___0);
//assert(__retres1 == rsp_tt_type);
//assert(__retres1 == rsp_t_type);
//assert(__retres1 == req_t_d);
//assert(__retres1 == req_t_d___0);
//assert(__retres1 == rsp_t_status);
assert(c_empty_req == s_run_i);
//assert(__retres1 == c_req_a);
//assert(__retres1 == c_req_type);
//assert(__retres1 == c_req_d);
//assert(__retres1 == s_run_st);
//assert(__retres1 == a_t);
//assert(__retres1 == 0);
//assert(__retres1 == c_m_lock);
//assert(__retres1 == req_t_type___0);
//assert(__retres1 == c_write_rsp_ev);
//assert(__retres1 == req_t_type);
//assert(__retres1 == c_read_req_ev);
//assert(__retres1 == m_run_st);
//assert(__retres1 == s_memory0);
assert(c_m_ev == 2);
//assert(__retres1 == c_read_rsp_ev);
          _L___7: /* CIL Label */ 
          if ((int )m_run_pc == 4) {
//assert(__retres1 == rsp_t_type___0);
//assert(__retres1 == rsp_tt_d);
//assert(__retres1 == req_tt_a);
//assert(__retres1 == s_run_pc);
//assert(__retres1 == rsp_t_d);
assert(c_m_ev == c_write_req_ev);
//assert(__retres1 == m_run_pc);
//assert(__retres1 == req_tt_type);
assert(c_empty_req == 1);
//assert(__retres1 == c_rsp_status);
//assert(__retres1 == req_tt_d);
//assert(__retres1 == c_rsp_d);
//assert(__retres1 == c_rsp_type);
//assert(__retres1 == rsp_t_d___0);
//assert(__retres1 == d_t);
assert(c_empty_req == c_empty_rsp);
//assert(__retres1 == req_t_a);
assert(c_empty_req == m_run_i);
//assert(__retres1 == rsp_t_status___0);
//assert(__retres1 == req_t_a___0);
//assert(__retres1 == rsp_tt_type);
//assert(__retres1 == rsp_t_type);
//assert(__retres1 == req_t_d);
//assert(__retres1 == req_t_d___0);
//assert(__retres1 == rsp_t_status);
assert(c_empty_req == s_run_i);
//assert(__retres1 == c_req_a);
//assert(__retres1 == c_req_type);
//assert(__retres1 == c_req_d);
//assert(__retres1 == s_run_st);
assert(c_m_ev == c_read_req_ev);
//assert(__retres1 == a_t);
//assert(__retres1 == 0);
//assert(__retres1 == c_m_lock);
//assert(__retres1 == req_t_type___0);
//assert(__retres1 == c_write_rsp_ev);
//assert(__retres1 == req_t_type);
//assert(__retres1 == m_run_st);
//assert(__retres1 == s_memory0);
assert(c_m_ev == 2);
//assert(__retres1 == c_read_rsp_ev);
            if ((int )c_m_ev == 1) {
              m_run_st = 0;
//assert(__retres1 == rsp_t_type___0);
assert(c_m_ev == c_write_rsp_ev);
//assert(__retres1 == rsp_tt_d);
//assert(__retres1 == req_tt_a);
//assert(__retres1 == s_run_pc);
//assert(__retres1 == rsp_t_d);
assert(c_m_ev == c_write_req_ev);
//assert(__retres1 == m_run_pc);
//assert(__retres1 == req_tt_type);
assert(c_empty_req == 1);
//assert(__retres1 == c_rsp_status);
//assert(__retres1 == req_tt_d);
//assert(__retres1 == c_rsp_d);
//assert(__retres1 == c_rsp_type);
//assert(__retres1 == rsp_t_d___0);
//assert(__retres1 == d_t);
assert(c_empty_req == c_empty_rsp);
//assert(__retres1 == req_t_a);
assert(c_empty_req == m_run_i);
//assert(__retres1 == req_t_a___0);
//assert(__retres1 == rsp_t_status___0);
//assert(__retres1 == rsp_tt_type);
//assert(__retres1 == rsp_t_type);
//assert(__retres1 == req_t_d);
//assert(__retres1 == req_t_d___0);
//assert(__retres1 == rsp_t_status);
assert(c_empty_req == s_run_i);
//assert(__retres1 == c_req_a);
//assert(__retres1 == c_req_type);
//assert(__retres1 == c_req_d);
assert(c_m_ev == c_read_rsp_ev);
//assert(__retres1 == s_run_st);
assert(c_m_ev == c_read_req_ev);
//assert(__retres1 == a_t);
//assert(__retres1 == 0);
//assert(__retres1 == c_m_lock);
//assert(__retres1 == req_t_type___0);
//assert(__retres1 == req_t_type);
//assert(__retres1 == m_run_st);
//assert(__retres1 == s_memory0);
assert(c_m_ev == 2);
            } else {
//assert(__retres1 == rsp_t_type___0);
assert(c_m_ev == c_write_rsp_ev);
//assert(__retres1 == rsp_tt_d);
//assert(__retres1 == req_tt_a);
//assert(__retres1 == s_run_pc);
//assert(__retres1 == rsp_t_d);
assert(c_m_ev == c_write_req_ev);
//assert(__retres1 == m_run_pc);
//assert(__retres1 == req_tt_type);
assert(c_empty_req == 1);
//assert(__retres1 == c_rsp_status);
//assert(__retres1 == req_tt_d);
//assert(__retres1 == c_rsp_d);
//assert(__retres1 == c_rsp_type);
//assert(__retres1 == rsp_t_d___0);
//assert(__retres1 == d_t);
assert(c_empty_req == c_empty_rsp);
//assert(__retres1 == req_t_a);
assert(c_empty_req == m_run_i);
//assert(__retres1 == req_t_a___0);
//assert(__retres1 == rsp_t_status___0);
//assert(__retres1 == rsp_tt_type);
//assert(__retres1 == rsp_t_type);
//assert(__retres1 == req_t_d);
//assert(__retres1 == req_t_d___0);
//assert(__retres1 == rsp_t_status);
assert(c_empty_req == s_run_i);
//assert(__retres1 == c_req_a);
//assert(__retres1 == c_req_type);
//assert(__retres1 == c_req_d);
assert(c_m_ev == c_read_rsp_ev);
//assert(__retres1 == s_run_st);
assert(c_m_ev == c_read_req_ev);
//assert(__retres1 == a_t);
//assert(__retres1 == 0);
//assert(__retres1 == c_m_lock);
//assert(__retres1 == req_t_type___0);
//assert(__retres1 == req_t_type);
//assert(__retres1 == m_run_st);
//assert(__retres1 == s_memory0);
assert(c_m_ev == 2);
              goto _L___6;
            }
//assert(__retres1 == rsp_t_type___0);
assert(c_m_ev == c_write_rsp_ev);
//assert(__retres1 == rsp_tt_d);
//assert(__retres1 == req_tt_a);
//assert(__retres1 == s_run_pc);
//assert(__retres1 == rsp_t_d);
assert(c_m_ev == c_write_req_ev);
//assert(__retres1 == m_run_pc);
//assert(__retres1 == req_tt_type);
assert(c_empty_req == 1);
//assert(__retres1 == c_rsp_status);
//assert(__retres1 == req_tt_d);
//assert(__retres1 == c_rsp_d);
//assert(__retres1 == c_rsp_type);
//assert(__retres1 == rsp_t_d___0);
//assert(__retres1 == d_t);
assert(c_empty_req == c_empty_rsp);
//assert(__retres1 == req_t_a);
assert(c_empty_req == m_run_i);
//assert(__retres1 == req_t_a___0);
//assert(__retres1 == rsp_t_status___0);
//assert(__retres1 == rsp_tt_type);
//assert(__retres1 == rsp_t_type);
//assert(__retres1 == req_t_d);
//assert(__retres1 == req_t_d___0);
//assert(__retres1 == rsp_t_status);
assert(c_empty_req == s_run_i);
//assert(__retres1 == c_req_a);
//assert(__retres1 == c_req_type);
//assert(__retres1 == c_req_d);
assert(c_m_ev == c_read_rsp_ev);
//assert(__retres1 == s_run_st);
assert(c_m_ev == c_read_req_ev);
//assert(__retres1 == a_t);
//assert(__retres1 == 0);
//assert(__retres1 == c_m_lock);
//assert(__retres1 == req_t_type___0);
//assert(__retres1 == req_t_type);
//assert(__retres1 == m_run_st);
//assert(__retres1 == s_memory0);
assert(c_m_ev == 2);
          } else {
            //assert(__retres1 == rsp_t_type___0);
assert(c_m_ev == c_write_rsp_ev);
//assert(__retres1 == rsp_tt_d);
//assert(__retres1 == req_tt_a);
//assert(__retres1 == s_run_pc);
//assert(__retres1 == rsp_t_d);
assert(c_m_ev == c_write_req_ev);
//assert(__retres1 == m_run_pc);
//assert(__retres1 == req_tt_type);
assert(c_empty_req == 1);
//assert(__retres1 == c_rsp_status);
//assert(__retres1 == req_tt_d);
//assert(__retres1 == c_rsp_d);
//assert(__retres1 == c_rsp_type);
//assert(__retres1 == rsp_t_d___0);
//assert(__retres1 == d_t);
assert(c_empty_req == c_empty_rsp);
//assert(__retres1 == req_t_a);
assert(c_empty_req == m_run_i);
//assert(__retres1 == req_t_a___0);
//assert(__retres1 == rsp_t_status___0);
//assert(__retres1 == rsp_tt_type);
//assert(__retres1 == rsp_t_type);
//assert(__retres1 == req_t_d);
//assert(__retres1 == req_t_d___0);
//assert(__retres1 == rsp_t_status);
assert(c_empty_req == s_run_i);
//assert(__retres1 == c_req_a);
//assert(__retres1 == c_req_type);
//assert(__retres1 == c_req_d);
assert(c_m_ev == c_read_rsp_ev);
//assert(__retres1 == s_run_st);
assert(c_m_ev == c_read_req_ev);
//assert(__retres1 == a_t);
//assert(__retres1 == 0);
//assert(__retres1 == c_m_lock);
//assert(__retres1 == req_t_type___0);
//assert(__retres1 == req_t_type);
//assert(__retres1 == m_run_st);
//assert(__retres1 == s_memory0);
assert(c_m_ev == 2);
_L___6: /* CIL Label */ 
            //assert(__retres1 == rsp_t_type___0);
assert(c_m_ev == c_write_rsp_ev);
//assert(__retres1 == rsp_tt_d);
//assert(__retres1 == req_tt_a);
//assert(__retres1 == s_run_pc);
//assert(__retres1 == rsp_t_d);
assert(c_m_ev == c_write_req_ev);
//assert(__retres1 == m_run_pc);
//assert(__retres1 == req_tt_type);
assert(c_empty_req == 1);
//assert(__retres1 == c_rsp_status);
//assert(__retres1 == req_tt_d);
//assert(__retres1 == c_rsp_d);
//assert(__retres1 == c_rsp_type);
//assert(__retres1 == rsp_t_d___0);
//assert(__retres1 == d_t);
assert(c_empty_req == c_empty_rsp);
//assert(__retres1 == req_t_a);
assert(c_empty_req == m_run_i);
//assert(__retres1 == req_t_a___0);
//assert(__retres1 == rsp_t_status___0);
//assert(__retres1 == rsp_tt_type);
//assert(__retres1 == rsp_t_type);
//assert(__retres1 == req_t_d);
//assert(__retres1 == req_t_d___0);
//assert(__retres1 == rsp_t_status);
assert(c_empty_req == s_run_i);
//assert(__retres1 == c_req_a);
//assert(__retres1 == c_req_type);
//assert(__retres1 == c_req_d);
assert(c_m_ev == c_read_rsp_ev);
//assert(__retres1 == s_run_st);
assert(c_m_ev == c_read_req_ev);
//assert(__retres1 == a_t);
//assert(__retres1 == 0);
//assert(__retres1 == c_m_lock);
//assert(__retres1 == req_t_type___0);
//assert(__retres1 == req_t_type);
//assert(__retres1 == m_run_st);
//assert(__retres1 == s_memory0);
assert(c_m_ev == 2);
if ((int )m_run_pc == 5) {
              if ((int )c_read_req_ev == 1) {
                m_run_st = 0;
              } else {
                goto _L___5;
              }
            } else {
              _L___5: /* CIL Label */ 
              if ((int )m_run_pc == 6) {
                if ((int )c_write_rsp_ev == 1) {
                  m_run_st = 0;
                } else {

                }
              } else {

              }
            }
          }
        }
      }
    }
    if ((int )s_run_pc == 2) {
      if ((int )c_write_req_ev == 1) {
        s_run_st = 0;
      } else {
        goto _L___10;
      }
    } else {
      _L___10: /* CIL Label */ 
      if ((int )s_run_pc == 1) {
        if ((int )c_read_rsp_ev == 1) {
          s_run_st = 0;
        } else {

        }
      } else {

      }
    }
    if ((int )m_run_st == 0) {

    } else {
      if ((int )s_run_st == 0) {

      } else {
        goto while_12_break;
      }
    }
  }
  while_12_break: /* CIL Label */ ;
  }

  return;
}
}
int __retres1 ;
int main(void) 
{ 
// XXX Modified AEJ
  int foo;
  {
  {
 c_m_lock  =    0;
 c_m_ev  =    2;

  m_run_i = 1;
  m_run_pc = 0;
  s_run_i = 1;
  s_run_pc = 0;
  c_empty_req = 1;
  c_empty_rsp = 1;
  c_read_req_ev = 2;
  c_write_req_ev = 2;
  c_read_rsp_ev = 2;
  c_write_rsp_ev = 2;
  c_m_lock = 0;
  c_m_ev = 2;
  start_simulation();
  }
  __retres1 = 0;
  return (__retres1);
}
}
