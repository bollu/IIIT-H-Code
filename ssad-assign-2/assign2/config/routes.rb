Rails.application.routes.draw do
  get 'admin/login'
  get 'admin/logout'
  get 'admin/mainpage'
  
  # SURVEYS
  get 'admin/new_survey'
  post 'admin/new_survey' => 'admin#new_survey'

  get 'admin/survey_add_question'
  post 'admin/survey_add_question' => 'admin#survey_add_question'

  post 'admin/login' => 'admin#login'
  
  delete 'admin/logout' => 'admin#logout'
  get 'admin/logout' => 'admin#logout'
    


  get 'user/signup'
  get 'user/login'
  get 'user/mainpage'

  post 'user/signup' => 'user#signup'
  post 'user/login' => 'user#login'
  delete 'user/logout' => 'user#logout'
  delete 'user/delete_user' => 'user#delete_user'

  get 'user/logout' => 'user#logout'
    

end
