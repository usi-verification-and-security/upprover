#ifndef REPORTER_H
#define REPORTER_H

#include <iostream>
#include <sstream>
#include <stdlib.h>

class Reportert {
public:
    Reportert()
    {
        // Redirect all output into a buffer
        m_out_report.rdbuf(&m_reporter_buf);
    }
    
    ~Reportert() { }
    
    void end_stage(std::ostream& out)
    {
        // Print all before cleaning the object
        m_out_report.flush();
        out << m_reporter_buf.str() << "\n";
        out.flush();
    }
    
    // Prints general status information
    std::ostream &status()
    {
        return m_out_report;
    }
    
#ifdef DISABLE_OPTIMIZATIONS    
    // Debug - only to be used in the none-official version
    std::ostream &debug()
    {
        return out_report;
    }
#endif
    
    // Report init/start
    virtual void report_start()=0;
    
    // Final reports for fail or success cases
    virtual void report_successful()=0;
    virtual void report_fail()=0;
    
protected:
    std::ostream m_out_report(0);
    std::stringbuf m_reporter_buf;
};

#endif /* REPORTER_H */